"""Regressions found by real-world testing of the SMT/SAT backends, the PoT IR and SMT patterns."""

from __future__ import annotations

import pytest

from formalkit import Verdict, backend, docker
from formalkit.adapters._smtlib import classify, unfence


def need(*names):
    missing = [n for n in names if not docker.has_image(n)]
    if missing:
        pytest.skip(f"images not built: {missing}")
    return [backend(n) for n in names]


# -- classifier (no Docker) ---------------------------------------------------------------


def test_multiline_unsat_core_is_parsed():  # cvc5 prints cores one name per line
    assert classify("unsat\n(\na\nb\n)").core == ["a", "b"]


def test_core_after_model_error():
    assert classify('unsat\n(error "line 3: model is not available")\n(a b)').core == ["a", "b"]


def test_get_value_fills_the_model():
    r = classify("sat\n((x 3)\n ((+ x 1) 4))")
    assert r.model == {"x": "3", "(+ x 1)": "4"}


def test_bounded_objectives_are_optimal_unbounded_are_not():
    assert classify("sat\n(objectives\n (x 9)\n)").verdict is Verdict.OPTIMAL
    assert classify("sat\n(objectives\n (x oo)\n)").verdict is Verdict.SAT
    assert classify("sat\n(objectives\n (x (+ 10.0 (* (- 1.0) epsilon)))\n)").verdict is Verdict.SAT


def test_unfence():
    assert unfence("```smt2\n(check-sat)\n```").strip() == "(check-sat)"
    assert unfence("(check-sat)") == "(check-sat)"


# -- through the real solvers ------------------------------------------------------------------



@pytest.mark.docker
def test_echo_cannot_spoof_a_verdict():
    (z3,) = need("z3")
    assert z3.run('(check-sat)\n(echo "unsat")').verdict is Verdict.SAT


@pytest.mark.docker
@pytest.mark.parametrize("name", ["z3", "cvc5"])
def test_incremental_scripts(name):
    (b,) = need(name)
    r = b.run("(declare-const x Int)(push 1)(assert (> x 1))(assert (< x 0))(check-sat)(pop 1)(check-sat)")
    assert r.verdict is Verdict.SAT and r.details["check_sat"] == ["unsat", "sat"]


@pytest.mark.docker
@pytest.mark.parametrize("name", ["z3", "cvc5"])
def test_unsat_core_both_solvers(name):
    (b,) = need(name)
    r = b.run("(set-option :produce-unsat-cores true)(declare-const x Int)(assert (! (> x 1) :named a))"
              "(assert (! (< x 0) :named b))(check-sat)(get-unsat-core)")  # fmt: skip
    assert r.verdict is Verdict.UNSAT and sorted(r.core) == ["a", "b"]


@pytest.mark.docker
@pytest.mark.parametrize("name", ["z3", "cvc5"])
def test_fenced_scripts_run(name):
    (b,) = need(name)
    assert b.run("```smt2\n(declare-const x Int)(assert (> x 1))(check-sat)\n```").verdict is Verdict.SAT


@pytest.mark.docker
def test_z3_optimum():
    (z3,) = need("z3")
    r = z3.run("(declare-const x Int)(assert (< x 10))(maximize x)(check-sat)(get-objectives)")
    assert r.verdict is Verdict.OPTIMAL and r.details["objectives"] == {"x": "9"}
    assert z3.run("(declare-const x Int)(maximize x)(check-sat)(get-objectives)").verdict is Verdict.SAT


# -- DIMACS ------------------------------------------------------------------------------------


def test_dimacs_header_is_rederived():
    from formalkit.adapters.kissat import normalize

    cnf, note = normalize("p cnf 2 5\n1 2 0\n")
    assert cnf.splitlines()[-2:] == ["p cnf 2 1", "1 2 0"] and "did not match" in note
    assert normalize("p cnf 5 1\n1 0\n")[1] == ""  # extra declared variables are legal
    assert "no 'p cnf' header" in normalize("1 0\n-1 0\n")[1]
    assert "not terminated" in normalize("p cnf 1 1\n1\n")[1]
    with pytest.raises(ValueError, match="empty input"):
        normalize("c nothing\n")
    with pytest.raises(ValueError, match="not an integer"):
        normalize("p cnf 1 1\nx 0\n")
    assert normalize("```\np cnf 1 1\n1 0\n```")[0].endswith("p cnf 1 1\n1 0\n")


@pytest.mark.docker
def test_kissat_tolerates_llm_dimacs():
    (k,) = need("kissat")
    r = k.run("c miscounted\np cnf 1 9\n1 0\n-1 0\n")
    assert r.verdict is Verdict.UNSAT and r.proof["checked"] and "did not match" in r.output
    assert k.run("").verdict is Verdict.ERROR


# -- check.py: uniqueness and equivalence edge cases ------------------------------------------


@pytest.mark.docker
@pytest.mark.parametrize(
    "script,verdict",
    [
        ("(declare-const |a b| Int)(assert (= |a b| 3))(check-sat)", Verdict.PROVED),  # quoted symbols
        ("(declare-const x Int)(assert (= x 3))(check-sat)(get-value (x (+ x 1)))", Verdict.PROVED),  # get-value terms
        ("(declare-const x Int)(assert (= x 3))(check-sat)(exit)", Verdict.PROVED),  # (exit) stripped
        ("(declare-const x Int)(assert (> x 3))(check-sat)(exit)", Verdict.REFUTED),
        ('(declare-const s String)(assert (= s "a""b"))(check-sat)', Verdict.PROVED),
    ],
)
def test_unique_edge_cases(script, verdict):
    from formalkit.patterns import unique

    (z3,) = need("z3")
    assert unique(z3, script).verdict is verdict


@pytest.mark.docker
def test_equivalence_edge_cases():
    from formalkit.patterns import smt_equivalent

    (z3,) = need("z3")
    lia = "(set-logic QF_LIA)(declare-const x Int)(assert (> x 0))"
    nia = "(set-logic QF_NIA)(declare-const x Int)(assert (>= x 1))"
    assert smt_equivalent(z3, lia, nia).verdict is Verdict.PROVED  # different set-logic lines
    scoped = smt_equivalent(z3, "(declare-const x Int)(push 1)(assert (> x 0))(pop 1)", "(declare-const x Int)")
    assert scoped.verdict is Verdict.ERROR and "push/pop" in scoped.output


# -- PoT IR: bit-vectors, as z3py interprets them ----------------------------------------------

BV_EXPRS = ["a + b == 3", "a + 1 == BitVecVal(-1, 8)", "a < b", "a <= b", "a > b", "a >= b", "ULT(a, b)", "UGE(a, b)",
            "~a == a ^ b", "-a == a >> 1", "a << 2 == a | b", "a & b == 0", "Concat(a, b) == w",
            "Extract(3, 0, a) == Extract(7, 4, b)", "ZeroExt(8, a) == w", "SignExt(8, a) == w",
            "UDiv(a, 2) == LShR(a, 1)", "a % 3 == 1", "a / 3 == b", "URem(a, 3) == SRem(b, 3)", "a * 300 == 44",
            "Sum([a, b, 1]) == 3", "Product(a, b) == 6", "Sum([1, a]) == 2", "If(a > b, a, 0) == b"]  # fmt: skip


def _bv_assertion(expr):
    import json

    from formalkit.ir import pot

    smt = pot.compile(json.dumps({
        "functions": [{"name": "a", "domain": [], "range": "BitVecSort(8)"},  # inline sort references
                      {"name": "b", "domain": [], "range": "BitVecSort(8)"},
                      {"name": "w", "domain": [], "range": "BitVecSort(16)"}],
        "knowledge_base": [expr], "verifications": [{"name": "v", "constraint": "True"}]}))  # fmt: skip
    return next(line for line in smt.splitlines() if line.startswith("(assert"))[len("(assert ") : -1]


def test_pot_bitvector_translation():
    assert _bv_assertion("a + 1 == BitVecVal(-1, 8)") == "(= (bvadd a (_ bv1 8)) (_ bv255 8))"
    assert _bv_assertion("a < b") == "(bvslt a b)"  # z3py's < on bit-vectors is signed
    assert _bv_assertion("Extract(3, 0, a) == Extract(7, 4, b)") == "(= ((_ extract 3 0) a) ((_ extract 7 4) b))"


@pytest.mark.parametrize(
    "expr,message",
    [("a + w == 1", "widths differ"), ("a + 1.5 == 1", "cannot mix"), ("Extract(9, 0, a) == 1", "out of range"),
     ("~x == 1", "unknown symbol")],  # fmt: skip
)
def test_pot_bitvector_errors(expr, message):
    from formalkit.ir import pot

    with pytest.raises(pot.PoTError, match=message):
        _bv_assertion(expr)


@pytest.mark.docker
def test_pot_bitvectors_mean_what_z3py_means():
    """Each compiled expression is proved equivalent to z3py's own reading of it, inside the z3 image."""
    import json
    import subprocess

    need("z3")
    pairs = [(e, _bv_assertion(e)) for e in BV_EXPRS]
    checker = (
        "import json, sys\nfrom z3 import *\na, b = BitVecs('a b', 8); w = BitVec('w', 16)\nbad = []\n"
        "for e, ours in json.load(sys.stdin):\n"
        "    mine = parse_smt2_string('(declare-fun a () (_ BitVec 8))(declare-fun b () (_ BitVec 8))'\n"
        "                             '(declare-fun w () (_ BitVec 16))(assert ' + ours + ')')[0]\n"
        "    s = Solver(); s.add(mine != eval(e))\n"
        "    if s.check() != unsat: bad.append(e)\n"
        "print(json.dumps(bad))\n"
    )
    out = subprocess.run(["docker", "run", "--rm", "-i", docker.image("z3"), "python3", "-c", checker],
                         input=json.dumps(pairs), capture_output=True, text=True, timeout=120)  # fmt: skip
    assert json.loads(out.stdout) == [], out.stderr


@pytest.mark.docker
def test_pot_bitvector_program_runs():
    import json

    (pot_backend,) = [backend("pot")] if docker.has_image("z3") else need("z3")
    program = json.dumps({
        "functions": [{"name": "x", "domain": [], "range": "BitVecSort(8)"}],
        "knowledge_base": ["x == 200 + 100"],
        "verifications": [{"name": "wraps", "constraint": "x != 44"}]})  # fmt: skip
    assert pot_backend.run(program).verdict is Verdict.UNSAT  # 300 wraps to 44 in 8 bits


@pytest.mark.docker
def test_z3_timeout_is_unknown():
    (z3,) = need("z3")
    hard = ("(declare-const a Int)(declare-const b Int)(declare-const c Int)(assert (> a 0))(assert (> b 0))"
            "(assert (> c 0))(assert (= (+ (* a a a) (* b b b)) (* c c c)))(check-sat)(get-info :reason-unknown)")  # fmt: skip
    r = z3.run(hard, timeout=2)
    assert r.verdict is Verdict.UNKNOWN and r.details.get("timeout") and '"timeout"' in r.output


@pytest.mark.parametrize(
    "expr,assertion",
    [("x == 200 + 100", "(= x (_ bv44 8))"), ("y == 7 / 2", "(= y 3.5)"), ("y == 2 ** 10", "(= y 1024)"),
     ("z == 7 // 2", "(= z 3)"), ("z == -(3 - 10)", "(= z 7)")],  # fmt: skip
)
def test_pot_folds_literal_arithmetic_like_python(expr, assertion):
    import json

    from formalkit.ir import pot

    smt = pot.compile(json.dumps({
        "variables": [{"name": "z", "sort": "IntSort"}, {"name": "y", "sort": "RealSort"}],
        "functions": [{"name": "x", "domain": [], "range": "BitVecSort(8)"}],
        "knowledge_base": [expr], "verifications": [{"name": "v", "constraint": "True"}]}))  # fmt: skip
    assert f"(assert {assertion})" in smt


def test_pot_literal_division_by_zero():
    import json

    from formalkit.ir import pot

    with pytest.raises(pot.PoTError, match="division by zero"):
        pot.compile(json.dumps({"variables": [{"name": "z", "sort": "IntSort"}], "knowledge_base": ["z == 1 / 0"],
                                "verifications": [{"name": "v", "constraint": "True"}]}))  # fmt: skip


def test_pot_nullary_functions_apply_like_z3py():
    import json

    from formalkit.ir import pot

    smt = pot.compile(json.dumps({"functions": [{"name": "sides", "domain": [], "range": "IntSort"}],
                                  "knowledge_base": ["sides() == 6", "sides > 5"],
                                  "verifications": [{"name": "v", "constraint": "True"}]}))  # fmt: skip
    assert "(assert (= sides 6))" in smt and "(assert (> sides 5))" in smt


def test_pot_rejects_numeric_constant_names():
    import json

    from formalkit.ir import pot

    with pytest.raises(pot.PoTError, match="not a valid name"):
        pot.compile(json.dumps({"constants": {"n": {"sort": "IntSort", "members": ["366"]}},
                                "verifications": [{"name": "v", "constraint": "True"}]}))  # fmt: skip


@pytest.mark.docker
def test_instantiate_dedupes_and_validates_in_parallel():
    from conftest import ScriptedClient

    from formalkit import LLM
    from formalkit.patterns import instantiate

    (z3,) = need("z3")
    n = 100  # z3 gives up on this chain by itself
    script = (f"(declare-fun s (Int) Int)\n(assert (= (s 0) 0))\n"
              f"(assert (forall ((n Int)) (=> (> n 0) (= (s n) (+ (s (- n 1)) n)))))\n"
              f"(assert (not (= (s {n}) {n * (n + 1) // 2})))\n(check-sat)")  # fmt: skip
    assert z3.run(script, timeout=8).verdict is Verdict.UNKNOWN
    chain = "\n".join(f"(assert (= (s {k}) (+ (s {k - 1}) {k})))" for k in range(1, n + 1))
    llm = LLM(ScriptedClient([(f"```\n{chain}\n{chain}\n(assert (= (s 1) 7))\n```", None)]), "m")
    out = instantiate(llm, z3, script)
    assert len(out.accepted) == n and out.rejected == ["(assert (= (s 1) 7))"]
    assert out.result.verdict is Verdict.UNSAT


# -- soft facts ------------------------------------------------------------------------------------


@pytest.mark.docker
def test_soft_facts_match_keys_regardless_of_spacing():
    from conftest import ScriptedClient

    from formalkit import LLM
    from formalkit.patterns import soft_facts

    (problog,) = need("problog")
    llm = LLM(ScriptedClient([('{"likes(bob, sushi)": 0.9}', None)]), "m")
    out = soft_facts(llm, problog, "?::likes(bob,   sushi).\nquery(likes(bob,sushi)).\n")
    assert out.scores == {"likes(bob,   sushi)": 0.9} and out.result.model["likes(bob,sushi)"] == pytest.approx(0.9)


def test_soft_facts_must_be_ground():
    from conftest import Fixed

    from formalkit import LLM
    from formalkit.patterns import soft_facts

    problog = Fixed("problog", lambda code: (Verdict.SAT,))
    out = soft_facts(LLM(None, "m"), problog, "?::likes(X, jazz) :- person(X).\n?::capital('Paris', france).\n")
    assert out.result.verdict is Verdict.ERROR and "likes(X, jazz)" in out.result.output and "Paris" not in out.result.output


def test_dimacs_malformed_header_is_an_error():
    from formalkit.adapters.kissat import normalize

    for bad in ("p cnf 2 x\n1 0\n", "p dnf 2 1\n1 0\n", "p cnf 2\n1 0\n"):
        with pytest.raises(ValueError, match="malformed header"):
            normalize(bad)


@pytest.mark.parametrize("value,negated", [("false", True), ("False", True), (False, True), (0, True), ("true", False)])
def test_pot_string_truth_values(value, negated):
    import json

    from formalkit.ir import pot

    smt = pot.compile(json.dumps({"functions": [{"name": "p", "domain": [], "range": "BoolSort"}],
                                  "knowledge_base": [{"assertion": "p", "value": value}],
                                  "verifications": [{"name": "v", "constraint": "True"}]}))  # fmt: skip
    assert ("(assert (not p))" in smt) is negated and ("(assert p)" in smt) is not negated


def test_pot_rejects_unclear_truth_values():
    import json

    from formalkit.ir import pot

    with pytest.raises(pot.PoTError, match="must be true or false"):
        pot.compile(json.dumps({"functions": [{"name": "p", "domain": [], "range": "BoolSort"}],
                                "knowledge_base": [{"assertion": "p", "value": "maybe"}],
                                "verifications": [{"name": "v", "constraint": "True"}]}))  # fmt: skip


@pytest.mark.docker
def test_pot_unicode_names():
    import json

    need("z3")
    program = {"sorts": [{"name": "Persön", "type": "DeclareSort"}],
               "functions": [{"name": "glücklich", "domain": ["Persön"], "range": "BoolSort"}],
               "constants": {"leute": {"sort": "Persön", "members": ["jürgen"]}},
               "knowledge_base": ["glücklich(jürgen)"],
               "verifications": [{"name": "v", "constraint": "Not(glücklich(jürgen))"}]}  # fmt: skip
    assert backend("pot").run(json.dumps(program)).verdict is Verdict.UNSAT


def test_lns_skips_empty_neighborhoods():
    from conftest import Fixed

    from formalkit.patterns import lns

    calls = []

    def fake(code):
        calls.append(code)
        return (Verdict.SAT, "", {"model": {"x": 1}, "objective": 1})

    out = lns(lambda inc, hist: [] if not hist else ["nope"], Fixed("minizinc", fake), "solve maximize x;", rounds=2)
    assert len(calls) == 1 and out.history == [([], None), ([], None)]  # unknown names are not a neighborhood


@pytest.mark.docker
@pytest.mark.parametrize(
    "name,code,tip",
    [("cvc5", "(set-logic ALL_SUPPORTED)(declare-const x Int)(check-sat)", "not an SMT-LIB logic"),
     ("cvc5", "(declare-const x Int)(set-logic QF_LIA)(check-sat)", "before any declaration"),
     ("cvc5", "(set-logic QF_LIA)(declare-const x Int)(assert (> (* x x) 1))(check-sat)", "nonlinear logic"),
     ("z3", "(set-logic HORN)(declare-const x Int)(assert (> x 1))(check-sat)", "special-purpose engine")],  # fmt: skip
)
def test_logic_traps_get_hints(name, code, tip):
    (b,) = need(name)
    assert tip in b.run(code).output.splitlines()[-1]


def test_llm_neighborhood_falls_back_to_random_when_reply_is_unusable():
    from conftest import ScriptedClient

    from formalkit import LLM
    from formalkit.patterns import llm_neighborhood

    incumbent = {f"x{i}": 0 for i in range(10)}
    propose = llm_neighborhood(LLM(ScriptedClient([("", None), ("", None)]), "m"), "model", k=3)
    picked = propose(incumbent, [])
    assert len(picked) == 3 and set(picked) <= set(incumbent)
    strict = llm_neighborhood(LLM(ScriptedClient([("", None)]), "m"), "model", k=3, fallback=False)
    assert strict(incumbent, []) == []


def test_pot_single_constant_shorthand():
    import json

    from formalkit.ir import pot

    smt = pot.compile(json.dumps({"constants": {"distance": {"sort": "IntSort"}},
                                  "knowledge_base": ["distance == 60 * 4 + 40 * 4"],
                                  "verifications": [{"name": "v", "constraint": "distance > 450"}]}))  # fmt: skip
    assert "(declare-const distance Int)" in smt and "(assert (= distance 400))" in smt


@pytest.mark.parametrize(
    "out,verdict",
    [("sat\n(\n  (define-fun s () S\n    Error)\n)\n((s Error))\nsat", Verdict.SAT),  # constructor named Error
     ("sat\n(\n  (define-fun v () T\n    (error 3))\n)\nsat", Verdict.SAT),  # constructor named error
     ('(error "line 1 column 12: unknown constant y")\nsat', Verdict.ERROR),
     ("unsupported\n; ignoring\nsat", Verdict.ERROR)],  # fmt: skip
)
def test_error_lines_are_matched_exactly(out, verdict):
    assert classify(out).verdict is verdict


@pytest.mark.docker
@pytest.mark.parametrize("name", ["z3", "cvc5"])
def test_error_named_constructors(name):
    (b,) = need(name)
    code = ("(declare-datatypes ((S 0)) (((Ok) (Error))))(declare-const s S)(assert (= s Error))"
            "(check-sat)(get-model)(get-value (s))(check-sat)")  # fmt: skip
    assert b.run(code).verdict is Verdict.SAT


@pytest.mark.docker
@pytest.mark.parametrize("name", ["z3", "cvc5"])
def test_get_proof_fills_the_proof_key(name):
    (b,) = need(name)
    code = "(set-option :produce-proofs true)(declare-const x Int)(assert (> x 5))(assert (< x 3))(check-sat)(get-proof)"
    r = b.run(code)
    assert r.verdict is Verdict.UNSAT and r.proof and "error" not in r.proof
    assert "proof" not in b.run(code.replace("(get-proof)", "")).details


def test_pot_quantifier_lists_may_name_declared_variables():
    import json

    from formalkit.ir import pot

    base = {"sorts": [{"name": "P", "type": "DeclareSort"}], "functions": [{"name": "f", "domain": ["P"], "range": "BoolSort"}],
            "variables": [{"name": "p", "sort": "P"}], "verifications": [{"name": "v", "constraint": "True"}]}  # fmt: skip
    smt = pot.compile(json.dumps({**base, "rules": [{"forall": ["p"], "constraint": "f(p)"}]}))
    assert "(assert (forall ((p P)) (f p)))" in smt
    with pytest.raises(pot.PoTError, match="not declared under 'variables'"):
        pot.compile(json.dumps({**base, "rules": [{"forall": ["q"], "constraint": "f(q)"}]}))


_V = [{"name": "v", "constraint": "True"}]


@pytest.mark.parametrize(
    "program,message",
    [({"functions": "abc", "verifications": _V}, "'functions' must be a list"),
     ({"functions": [{"name": "f", "domain": "IntSort", "range": "BoolSort"}], "verifications": _V}, "'domain' of f"),
     ({"knowledge_base": {"a": 1}, "verifications": _V}, "'knowledge_base' must be a list"),
     ({"rules": [{"forall": [{"name": "x", "sort": "IntSort"}], "implies": "x > 0"}], "verifications": _V}, "'implies' must"),
     ({"verifications": ["True"]}, "items of 'verifications' must be objects"),
     ({"verifications": {"name": "v", "constraint": "True"}}, "'verifications' must be a list"),
     ({"constants": {"c": {"sort": "IntSort", "members": "abc"}}, "verifications": _V}, "'members' of constants"),
     ({"sorts": [{"name": "C", "type": "EnumSort", "values": "red"}], "verifications": _V}, "EnumSort C needs"),
     ({"functions": [{"name": 5, "domain": [], "range": "IntSort"}], "verifications": _V}, "not a valid name"),
     ({"verifications": [{"name": "v", "exists": "x", "constraint": "True"}]}, "must be a list of variables")],  # fmt: skip
)
def test_pot_malformed_shapes_are_explained_not_misread(program, message):
    import json

    from formalkit.ir import pot

    with pytest.raises(pot.PoTError, match=message):
        pot.compile(json.dumps(program))


def test_pot_compiler_only_raises_poterror_under_fuzzing():
    import json
    import random

    from formalkit.ir import pot

    base = json.loads(pot.EXAMPLE)
    junk = ["x", 5, None, [], {}, ["a"], {"a": 1}, True, "IntSort", [{"name": 3}], "Not(", "f(", "__import__('os')"]
    rnd = random.Random(0)

    def mutate(value, depth=0):
        if depth > 3 or rnd.random() < 0.2:
            return rnd.choice(junk)
        if isinstance(value, dict):
            return {k: mutate(v, depth + 1) if rnd.random() < 0.3 else v for k, v in value.items()}
        if isinstance(value, list):
            return [mutate(v, depth + 1) if rnd.random() < 0.3 else v for v in value]
        return value

    for _ in range(3000):
        try:
            pot.compile(json.dumps(mutate(base)))
        except pot.PoTError:
            pass


@pytest.mark.parametrize("expr", ["x == 1e309", "x == -1e309", "x == float('nan')"])
def test_pot_non_finite_numbers(expr):
    import json

    from formalkit.ir import pot

    with pytest.raises(pot.PoTError):
        pot.compile(json.dumps({"variables": [{"name": "x", "sort": "RealSort"}], "knowledge_base": [expr],
                                "verifications": [{"name": "v", "constraint": "True"}]}))  # fmt: skip


@pytest.mark.docker
@pytest.mark.parametrize(
    "code,tip",
    [('(declare-const s String)(assert (str.in.re s (str.to.re "ab")))(check-sat)', "use str.to_re"),
     ("(declare-const a Bool)(declare-const b Bool)(assert (implies a b))(check-sat)", "use =>")],  # fmt: skip
)
def test_deprecated_names_get_hints(code, tip):
    (cvc5,) = need("cvc5")
    r = cvc5.run(code)
    assert r.verdict is Verdict.ERROR and tip in r.output.splitlines()[-1]


@pytest.mark.docker
def test_z3_optimum_without_get_objectives():
    (z3,) = need("z3")
    r = z3.run("(declare-const x Int)(assert (> x 3))(minimize x)(check-sat)(get-model)")
    assert r.verdict is Verdict.OPTIMAL and r.details["objectives"] == {"x": "4"} and r.model == {"x": "4"}
    assert z3.run("(declare-const x Int)(minimize x)(check-sat)").verdict is Verdict.SAT  # unbounded


@pytest.mark.parametrize(
    "out,verdict",
    [('unknown\n(error "line 13 column 10: model is not available")\nunsat', Verdict.UNSAT),
     ('sat\n(error "cannot get model unless model generation is enabled (try --produce-models)")\nunsat', Verdict.UNSAT),
     ('(error "line 1 column 12: unknown constant y")\nsat', Verdict.ERROR)],  # fmt: skip
)
def test_failed_queries_do_not_poison_later_verdicts(out, verdict):
    assert classify(out).verdict is verdict


@pytest.mark.docker
def test_llm_style_script_with_get_model_after_unknown():
    (z3,) = need("z3")
    script = """(set-logic UFLIA)
(declare-fun f (Int) Int)
(assert (forall ((x Int)) (= (f (f x)) x)))
(assert (= (f 1) 2))
(check-sat)
(get-model)
(push)
(assert (not (= (f 2) 1)))
(check-sat)
(pop)"""
    r = z3.run(script)
    assert r.verdict is Verdict.UNSAT and r.details["check_sat"][-1] == "unsat"


def test_pot_signed_bitvector_comparisons_and_user_precedence():
    import json

    from formalkit.ir import pot

    funcs = [{"name": "b", "domain": [], "range": "BitVecSort(8)"}]
    smt = pot.compile(json.dumps({"functions": funcs, "knowledge_base": ["SLT(b, BitVecVal(0, 8))"],
                                  "verifications": [{"name": "v", "constraint": "True"}]}))  # fmt: skip
    assert "(assert (bvslt b (_ bv0 8)))" in smt
    own = funcs + [{"name": "ULT", "domain": ["IntSort", "IntSort"], "range": "BoolSort"}]
    smt = pot.compile(json.dumps({"functions": own, "knowledge_base": ["ULT(1, 2)"],
                                  "verifications": [{"name": "v", "constraint": "True"}]}))  # fmt: skip
    assert "(assert (ULT 1 2))" in smt  # the user's function, not the bit-vector builtin


@pytest.mark.docker
@pytest.mark.parametrize(
    "a,b,message",
    [("(declare-const x Int)(assert (> x 1)", "(declare-const x Int)", "unbalanced"),
     ("(declare-const x Bool)(assert x x)", "(declare-const x Bool)(assert x)", "exactly one term"),
     ("(assert)", "(declare-const x Int)", "exactly one term")],  # fmt: skip
)
def test_malformed_scripts_never_prove_equivalence(a, b, message):
    from formalkit.patterns import smt_equivalent

    (z3,) = need("z3")
    r = smt_equivalent(z3, a, b)
    assert r.verdict is Verdict.ERROR and message in r.output


def test_differential_with_no_backends():
    from formalkit.patterns import differential

    assert not differential([], "(check-sat)").disagree


@pytest.mark.docker
def test_unique_never_drops_malformed_parts():
    from formalkit.patterns import unique

    (z3,) = need("z3")
    assert unique(z3, "(declare-const x Int)(check-sat)(assert (> x 1)").verdict is Verdict.ERROR


@pytest.mark.docker
def test_truncated_script_is_an_error_not_a_counterexample():
    (z3,) = need("z3")
    r = z3.run("(declare-const x Int)\n(assert (> x 1))\n(check-sat)\n(assert (not (> x")  # cut off mid-assertion
    assert r.verdict is Verdict.ERROR


@pytest.mark.docker
@pytest.mark.parametrize("name", ["z3", "cvc5"])
def test_unique_with_uninterpreted_sorts(name):
    from formalkit.patterns import unique

    (b,) = need(name)
    script = "(declare-sort P 0)(declare-const a P)(declare-const b P)(declare-const n Int)(assert (not (= a b)))(assert (= n 3))(check-sat)"
    r = unique(b, script)
    assert r.verdict is Verdict.PROVED and r.details["uncompared"] == ["a", "b"] and r.model == {"n": "3"}


@pytest.mark.docker
def test_cvc5_timeout_is_marked():
    (cvc5,) = need("cvc5")
    hard = ("(declare-const a Int)(declare-const b Int)(declare-const c Int)(assert (> a 0))(assert (> b 0))"
            "(assert (> c 0))(assert (= (+ (* a a a) (* b b b)) (* c c c)))(check-sat)")  # fmt: skip
    r = cvc5.run(hard, timeout=2)
    assert r.verdict is Verdict.UNKNOWN and r.details.get("timeout")
    quick = cvc5.run("(declare-fun f (Int) Int)(assert (forall ((x Int)) (> (f x) (* x x x))))"
                     "(assert (forall ((x Int)) (< (f x) 0)))(check-sat)", timeout=20)  # fmt: skip
    assert quick.verdict is Verdict.UNKNOWN and not quick.details.get("timeout")  # incomplete, not out of time


@pytest.mark.parametrize(
    "text,expected",
    [("Here is the script:\n```smt2\n(check-sat)\n```\nDone.", "(check-sat)\n"),
     ("(check-sat) ; uses ``` in a comment", "(check-sat) ; uses ``` in a comment"),
     ("```\n(check-sat)", "(check-sat)"),
     ("Sure!\n```\np cnf 1 1\n1 0\n```", "p cnf 1 1\n1 0\n")],  # fmt: skip
)
def test_unfence_with_prose(text, expected):
    assert unfence(text) == expected


@pytest.mark.parametrize(
    "out",
    ["sat\n(error \"Can't get-info :reason-unknown when the last result wasn't unknown!\")",
     'sat\n(error "line 1 column 64: command is only available in interactive mode, use command '
     '(set-option :interactive-mode true)")',
     'sat\n(error "line 1 column 72: check annotation that says unsat")'],  # fmt: skip
)
def test_info_and_annotation_errors_do_not_poison(out):
    assert classify(out).verdict is Verdict.SAT


@pytest.mark.docker
def test_cvc5_timeout_option_hint():
    (cvc5,) = need("cvc5")
    r = cvc5.run("(declare-const x Int)(set-option :timeout 1000)(assert (> x 1))(check-sat)")
    assert r.verdict is Verdict.ERROR and "does not support (set-option :timeout" in r.output


_ARRAYS = {"sorts": [{"name": "Arr", "type": "ArraySort(IntSort, IntSort)"},
                     {"name": "Grid", "type": "ArraySort(IntSort, ArraySort(IntSort, BoolSort))"}],  # nested
           "functions": [{"name": "a", "domain": [], "range": "Arr"}, {"name": "g", "domain": [], "range": "Grid"}],
           "variables": [{"name": "i", "sort": "IntSort"}]}  # fmt: skip


@pytest.mark.parametrize(
    "expr,assertion",
    [("a[0] == 1", "(= (select a 0) 1)"), ("Select(a, 1) > a[0]", "(> (select a 1) (select a 0))"),
     ("Store(a, 2, 5)[2] == 5", "(= (select (store a 2 5) 2) 5)"), ("g[1][2]", "(select (select g 1) 2)")],  # fmt: skip
)
def test_pot_arrays(expr, assertion):
    import json

    from formalkit.ir import pot

    smt = pot.compile(json.dumps({**_ARRAYS, "knowledge_base": [expr], "verifications": [{"name": "v", "constraint": "True"}]}))
    assert f"(assert {assertion})" in smt


@pytest.mark.parametrize("expr,message", [("a[True] == 1", "index must be Int"), ("i[0] == 1", "not an array"),
                                          ("Store(a, 0, True) == a", "value must be Int")])  # fmt: skip
def test_pot_array_type_errors(expr, message):
    import json

    from formalkit.ir import pot

    with pytest.raises(pot.PoTError, match=message):
        pot.compile(json.dumps({**_ARRAYS, "knowledge_base": [expr], "verifications": [{"name": "v", "constraint": "True"}]}))


@pytest.mark.docker
def test_pot_array_semantics():
    import json

    need("z3")
    program = {**_ARRAYS, "knowledge_base": ["a[0] == 1", "ForAll([i], Implies(i >= 0, a[i + 1] == a[i] + 1))"],
               "verifications": [{"name": "v", "constraint": "a[3] != 4"}]}  # fmt: skip
    assert backend("pot").run(json.dumps(program)).verdict is Verdict.UNSAT


@pytest.mark.docker
@pytest.mark.parametrize("name", ["z3", "cvc5"])
def test_unsat_assumptions_become_the_core(name):
    (b,) = need(name)
    r = b.run("(set-option :produce-unsat-assumptions true)(declare-const a Bool)(declare-const b Bool)"
              "(assert (=> a b))(check-sat-assuming (a (not b)))(get-unsat-assumptions)")  # fmt: skip
    assert r.verdict is Verdict.UNSAT and sorted(r.core) == ["(not b)", "a"]


def test_dimacs_sections_are_combined():
    from formalkit.adapters.kissat import normalize

    cnf, note = normalize("p cnf 3 2\n-1 3 0\n-2 3 0\n\np cnf 3 2\n1 0\n-3 0\n")
    assert "p cnf 3 4" in cnf and note == "combined 2 'p cnf' sections into 'p cnf 3 4'"


# -- LNS over array elements ------------------------------------------------------------------------

_KNAP = "array[1..4] of var 0..1: take;\nvar 0..9: x;\nconstraint sum(take) + x <= 5;\nsolve maximize sum(take) + 2 * x;\n"


def test_lns_frees_single_array_elements():
    from conftest import Fixed

    from formalkit.patterns import lns

    calls = []

    def fake(code):  # first solve: take=[1,1,1,1], x=0 (obj 4); any neighborhood freeing x finds obj 6
        calls.append(code)
        x_fixed = "constraint x = 0;" in code
        value = 4 if len(calls) == 1 or x_fixed else 6
        return (Verdict.SAT, "", {"model": {"take": [1, 1, 1, 1], "x": 0 if value == 4 else 1}, "objective": value})

    out = lns(lambda inc, hist: ["take[2]", "x"] if not hist else ["nope[1]"], Fixed("minizinc", fake), _KNAP, rounds=2)
    assert out.objective == 6 and out.empty == 1 and out.history[0][0] == ["take[2]", "x"]
    second = calls[1]
    assert "constraint take[2] =" not in second and "constraint take[1] = 1;" in second and "constraint x = 0;" not in second


def test_llm_neighborhood_accepts_element_and_array_names():
    from conftest import ScriptedClient

    from formalkit import LLM
    from formalkit.patterns import llm_neighborhood

    inc = {"take": [1, 0, 1, 0], "x": 2}
    propose = llm_neighborhood(LLM(ScriptedClient([('["take[3]", "x"]', None), ('["take"]', None)]), "m"), _KNAP, k=2)
    assert propose(inc, []) == ["take[3]", "x"]
    assert propose(inc, [([], None)]) == ["take[1]", "take[2]", "take[3]", "take[4]"]


@pytest.mark.docker
def test_element_fixes_are_valid_minizinc():
    from formalkit.patterns.control import freeable

    (mzn,) = need("minizinc")
    incumbent = {"take": [1, 0, 1, 0], "x": 2}
    units = freeable(incumbent, _KNAP)
    fixes = "\n".join(f"constraint {u} = {v};" for u, v in units.items() if u not in ("take[2]", "take[4]"))
    r = mzn.run(_KNAP + fixes, timeout=30)
    assert r.verdict is Verdict.OPTIMAL and r.model["take"][0] == 1 and r.model["take"][2] == 1 and r.model["x"] == 2
    assert r.model["take"][1] + r.model["take"][3] == 1  # the freed elements were re-optimized (either one)


def test_pot_if_branches_must_agree():
    import json

    from formalkit.ir import pot

    with pytest.raises(pot.PoTError, match="different sorts"):
        pot.compile(json.dumps({"variables": [{"name": "x", "sort": "IntSort"}], "knowledge_base": ["If(x > 0, x, True) == x"],
                                "verifications": [{"name": "v", "constraint": "True"}]}))  # fmt: skip


def test_pot_integer_literals_become_bitvector_arguments():
    import json

    from formalkit.ir import pot

    base = {"functions": [{"name": "f", "domain": ["BitVecSort(8)"], "range": "BoolSort"}],
            "variables": [{"name": "x", "sort": "IntSort"}], "verifications": [{"name": "v", "constraint": "True"}]}  # fmt: skip
    assert "(assert (f (_ bv255 8)))" in pot.compile(json.dumps({**base, "knowledge_base": ["f(-1)"]}))
    with pytest.raises(pot.PoTError, match="cannot mix"):
        pot.compile(json.dumps({**base, "knowledge_base": ["f(x)"]}))  # a symbolic Int is not coerced


def test_pot_bitvector_arrays_coerce_literals():
    import json

    from formalkit.ir import pot

    base = {"sorts": [{"name": "M", "type": "ArraySort(BitVecSort(8), BitVecSort(8))"}],
            "functions": [{"name": "m", "domain": [], "range": "M"}], "verifications": [{"name": "v", "constraint": "True"}]}  # fmt: skip
    smt = pot.compile(json.dumps({**base, "knowledge_base": ["Store(m, 1, 255)[1] == 7"]}))
    assert "(select (store m (_ bv1 8) (_ bv255 8)) (_ bv1 8))" in smt


def test_pot_knowledge_object_without_assertion():
    import json

    from formalkit.ir import pot

    with pytest.raises(pot.PoTError, match='needs an "assertion"'):
        pot.compile(json.dumps({"knowledge_base": [{"fact": "True"}], "verifications": [{"name": "v", "constraint": "True"}]}))


@pytest.mark.docker
def test_cvc5_optimization_points_to_z3():
    (cvc5,) = need("cvc5")
    r = cvc5.run("(declare-const x Int)(assert (< x 5))(maximize x)(check-sat)")
    assert r.verdict is Verdict.ERROR and "use the z3 backend" in r.output


@pytest.mark.docker
def test_instantiate_keeps_recursive_definitions_for_validation():
    from conftest import ScriptedClient

    from formalkit import LLM
    from formalkit.patterns import instantiate

    (z3,) = need("z3")
    script = ("(set-option :auto_config false)\n(set-option :smt.mbqi false)\n"
              "(define-fun-rec twice ((n Int)) Int (ite (<= n 0) 0 (+ 2 (twice (- n 1)))))\n"
              "(declare-fun P (Int) Bool)\n(declare-fun Q (Int) Bool)\n"
              "(assert (forall ((x Int)) (! (P (twice x)) :pattern ((Q x)))))\n(assert (not (P (twice 3))))\n(check-sat)")  # fmt: skip
    out = instantiate(LLM(ScriptedClient([("```\n(assert (P (twice 3)))\n```", None)]), "m"), z3, script)
    assert out.accepted == ["(assert (P (twice 3)))"] and out.result.verdict is Verdict.UNSAT


def test_soft_facts_reads_almost_json():
    from conftest import Fixed, ScriptedClient

    from formalkit import LLM
    from formalkit.patterns import soft_facts

    problog = Fixed("problog", lambda code: (Verdict.SAT, code))
    reply = '```json\n{\n  "rain": 0.3,  // fairly unlikely\n  "wind": 0.9,\n}\n```'
    out = soft_facts(LLM(ScriptedClient([(reply, None)]), "m"), problog, "?::rain.\n?::wind.\nquery(rain).\n")
    assert out.scores == {"rain": 0.3, "wind": 0.9} and "0.3::rain." in problog.runs[-1]


@pytest.mark.parametrize("expr,message", [("Distinct(x, p)", "share one sort"), ("Distinct(x)", "at least two")])
def test_pot_distinct_sorts(expr, message):
    import json

    from formalkit.ir import pot

    base = {"functions": [{"name": "p", "domain": [], "range": "BoolSort"}], "variables": [{"name": "x", "sort": "IntSort"}],
            "verifications": [{"name": "v", "constraint": "True"}]}  # fmt: skip
    with pytest.raises(pot.PoTError, match=message):
        pot.compile(json.dumps({**base, "knowledge_base": [expr]}))


@pytest.mark.docker
@pytest.mark.parametrize(
    "code,tip",
    [("(set-logic QF_NIA)(declare-fun f (Int) Int)(assert (forall ((x Int)) (> (f x) 0)))(check-sat)", "does not include"),
     ("(set-logic QF_LIA)(declare-const y Int)(assert (forall ((x Int)) (> x y)))(check-sat)", "does not include quantifiers"),
     ("(declare-const a Int)(assert (= (max a 3) 3))(check-sat)", "not SMT-LIB functions")],  # fmt: skip
)
def test_more_trap_hints(code, tip):
    (z3,) = need("z3")
    assert tip in z3.run(code).output.splitlines()[-1]
