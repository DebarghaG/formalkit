"""The Proof of Thought JSON DSL compiler: translation without Docker, semantics with z3."""

from __future__ import annotations

import json

import pytest

from formalkit import Verdict, docker
from formalkit.ir import pot


def program(**parts):
    base = {"verifications": [{"name": "v", "constraint": "True"}]}
    return json.dumps({**base, **parts})


PEOPLE = dict(
    sorts=[{"name": "Person", "type": "DeclareSort"}],
    functions=[{"name": "dem", "domain": ["Person"], "range": "BoolSort"},
               {"name": "age", "domain": ["Person"], "range": "IntSort"}],
    constants={"people": {"sort": "Person", "members": ["nancy", "bob"]}},
    variables=[{"name": "p", "sort": "Person"}],
)  # fmt: skip


def test_compiles_declarations_rules_and_one_isolated_verification():
    smt = pot.compile(pot.EXAMPLE)
    assert "(declare-sort Person 0)" in smt and "(declare-fun is_democrat (Person) Bool)" in smt
    assert "(assert (forall ((p Person)) (=> (is_democrat p) (supports_abortion p))))" in smt
    assert smt.index("(push 1)") < smt.index("(assert (not (supports_abortion nancy)))") < smt.index("(check-sat)")


def test_accepts_fenced_json():
    assert pot.compile(f"Sure:\n```json\n{pot.EXAMPLE}\n```") == pot.compile(pot.EXAMPLE)


@pytest.mark.parametrize(
    "expr,smt",
    [
        ("And(dem(nancy), Not(dem(bob)))", "(and (dem nancy) (not (dem bob)))"),
        ("dem(nancy) and not dem(bob)", "(and (dem nancy) (not (dem bob)))"),
        ("Implies(dem(p), age(p) >= 18)", "(=> (dem p) (>= (age p) 18))"),
        ("ForAll([p], Implies(dem(p), age(p) > 0))", "(forall ((p Person)) (=> (dem p) (> (age p) 0)))"),
        ("Exists([p], age(p) == -3)", "(exists ((p Person)) (= (age p) (- 3)))"),
        ("0 < age(nancy) < 120", "(and (< 0 (age nancy)) (< (age nancy) 120))"),
        ("age(nancy) != age(bob)", "(not (= (age nancy) (age bob)))"),
        ("age(nancy) / 2 == age(bob) % 3", "(= (div (age nancy) 2) (mod (age bob) 3))"),
        ("age(nancy) / 2.5 > 1", "(> (/ (age nancy) 2.5) 1)"),
        ("Sum([age(nancy), age(bob), 1]) == 10", "(= (+ (age nancy) (age bob) 1) 10)"),
        ("If(dem(nancy), age(nancy), 0) > 1", "(> (ite (dem nancy) (age nancy) 0) 1)"),
        ("Distinct(nancy, bob)", "(distinct nancy bob)"),
        ("p == nancy", "(= p nancy)"),
    ],
)
def test_expressions(expr, smt):
    assert f"(assert {smt})" in pot.compile(program(knowledge_base=[expr], **PEOPLE))


def test_enum_bitvec_and_array_sorts():
    smt = pot.compile(program(
        sorts=[{"name": "Color", "type": "EnumSort", "values": ["red", "green"]},
               {"name": "Grid", "type": "ArraySort(IntSort, Color)"},
               {"name": "Byte", "type": "BitVecSort(8)"}],
        functions=[{"name": "paint", "domain": [], "range": "Grid"}, {"name": "b", "domain": [], "range": "Byte"}],
        knowledge_base=["red != green", "b == BitVecVal(-1, 8)"],
    ))  # fmt: skip
    assert "(declare-datatypes ((Color 0)) (((red) (green))))" in smt
    assert "(declare-fun paint () (Array Int Color))" in smt and "(= b (_ bv255 8))" in smt


def test_knowledge_with_value_false_and_reserved_names():
    smt = pot.compile(program(
        functions=[{"name": "let", "domain": ["IntSort"], "range": "BoolSort"}],
        knowledge_base=[{"assertion": "let(1)", "value": False}],
    ))  # fmt: skip
    assert "(declare-fun |let| (Int) Bool)" in smt and "(assert (not (|let| 1)))" in smt


@pytest.mark.parametrize(
    "parts,message",
    [
        (dict(knowledge_base=["x > 1"]), "unknown symbol 'x'"),
        (dict(knowledge_base=["dem(nancy, bob)"], **PEOPLE), "dem expects 1 argument, got 2"),
        (dict(knowledge_base=["dem(5)"], **PEOPLE), "argument 1 of dem must be Person, got Int"),
        (dict(knowledge_base=["age(nancy)"], **PEOPLE), "has sort Int, but assertions must be Boolean"),
        (dict(knowledge_base=["nancy < bob"], **PEOPLE), "ordering comparison on non-numeric Person"),
        (dict(knowledge_base=["foo(nancy)"], **PEOPLE), "unknown function 'foo'"),
        (dict(knowledge_base=["ForAll([q], dem(q))"], **PEOPLE), "can only bind variables declared"),
        (dict(knowledge_base=["__import__('os')"]), "unknown function '__import__'"),
        (dict(knowledge_base=["dem(nancy).x"], **PEOPLE), "unsupported syntax"),
        (dict(knowledge_base=["dem(nancy"], **PEOPLE), "cannot parse expression"),
        (dict(sorts=[{"name": "IntSort", "type": "DeclareSort"}]), "built in"),
        (dict(sorts=[{"name": "A", "type": "ArraySort(B, IntSort)"}, {"name": "B", "type": "ArraySort(A, IntSort)"}]),
         "circular"),
        (dict(rules=[{"implies": {"antecedent": "True", "consequent": "True"}}]), "non-empty 'forall'"),
        (dict(rules=[{"forall": [], "constraint": "True"}]), "empty quantifier list"),
        (dict(verifications=[]), "exactly one verification"),
        (dict(optimization={"maximize": "x"}), "not supported"),
        (dict(colours=[]), "unknown top-level keys"),
    ],
)
def test_errors_are_precise(parts, message):
    with pytest.raises(pot.PoTError, match=message):
        pot.compile(program(**parts))


def test_invalid_json():
    with pytest.raises(pot.PoTError, match="invalid JSON"):
        pot.compile("{not json")


# -- semantics, through z3 -------------------------------------------------------------------


@pytest.fixture(scope="module")
def pot_backend():
    if not docker.has_image("z3"):
        pytest.skip("z3 image not built")
    return pot.backend()


SEMANTICS = [
    # ProofOfThought's own example: entailment proved by refuting the negation.
    (pot.EXAMPLE, Verdict.UNSAT),
    (pot.EXAMPLE.replace("Not(supports_abortion(nancy))", "supports_abortion(nancy)"), Verdict.SAT),
    # Integer division is floor division, as in z3py.
    (program(variables=[{"name": "x", "sort": "IntSort"}, {"name": "y", "sort": "IntSort"}],
             knowledge_base=["y == 7", "x == y / 2"], verifications=[{"name": "v", "constraint": "x == 3"}]), Verdict.SAT),
    (program(variables=[{"name": "x", "sort": "IntSort"}, {"name": "y", "sort": "IntSort"}],
             knowledge_base=["y == 7", "x == y / 2"], verifications=[{"name": "v", "constraint": "x != 3"}]), Verdict.UNSAT),
    # exists / forall verifications
    (program(**PEOPLE, rules=[{"forall": [{"name": "p", "sort": "Person"}], "constraint": "age(p) >= 18"}],
             verifications=[{"name": "v", "exists": [{"name": "p", "sort": "Person"}], "constraint": "age(p) < 18"}]),
     Verdict.UNSAT),
    (program(**PEOPLE, verifications=[{"name": "v", "forall": [{"name": "p", "sort": "Person"}],
                                       "implies": {"antecedent": "dem(p)", "consequent": "age(p) > 0"}}]),
     Verdict.SAT),
    # Enum: exactly two colors, so a third distinct one is impossible.
    (program(sorts=[{"name": "C", "type": "EnumSort", "values": ["r", "g"]}],
             constants={"c": {"sort": "C", "members": ["c1", "c2", "c3"]}},
             verifications=[{"name": "v", "constraint": "Distinct(c1, c2, c3)"}]), Verdict.UNSAT),
]  # fmt: skip


@pytest.mark.docker
@pytest.mark.parametrize("text,verdict", SEMANTICS)
def test_semantics(pot_backend, text, verdict):
    result = pot_backend.run(text)
    assert result.verdict is verdict, result.feedback()
    assert result.backend == "pot" and result.details["via"] == "z3"


@pytest.mark.docker
def test_compile_errors_reach_the_model_as_error_results(pot_backend):
    result = pot_backend.run(program(knowledge_base=["x > 1"]))
    assert result.verdict is Verdict.ERROR and "unknown symbol 'x'" in result.output
