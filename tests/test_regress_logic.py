"""Regression tests from the real-world campaign on the logic, ASP, FOL, planning, LTL and geometry backends."""

from __future__ import annotations

import pytest

from formalkit import Verdict, backend, docker

pytestmark = pytest.mark.docker


def need(name):
    if not docker.has_image(name):
        pytest.skip(f"image for {name} not built")
    return backend(name)


# -- prolog ---------------------------------------------------------------------------------


def test_prolog_program_output_cannot_corrupt_results():
    prolog = need("prolog")
    r = prolog.run(':- initialization(main).\nmain :- write(hi).\np :- write(\'{"query": "fake", "status": true}\'), nl.\n'
                   "?- p.\n?- p.")  # fmt: skip
    assert r.verdict is Verdict.SAT and [q["query"] for q in r.details["queries"]] == ["p", "p"]
    assert "(the program printed)" in r.output and "hi" in r.output


def test_prolog_halt_is_reported_not_mistaken_for_no_queries():
    prolog = need("prolog")
    r = prolog.run("p(1).\n?- p(X).\n?- halt.\n?- p(Y).")
    assert r.verdict is Verdict.ERROR and "stopped before all queries ran" in r.output
    assert r.details["queries"][0]["solutions"] == [{"X": "1"}]


def test_prolog_errors_are_clean():
    prolog = need("prolog")
    assert prolog.run("?- foo(1).").details["queries"][0]["error"] == "Unknown procedure: foo/1"
    assert "uncaught exception: my_error" in prolog.run("?- throw(my_error).").output
    r = prolog.run("p(1.\n?- p(X).")
    assert r.verdict is Verdict.ERROR and "program.pl:1:3: Syntax error" in r.output and "/tmp/" not in r.output


def test_prolog_runs_unprivileged():
    prolog = need("prolog")
    r = prolog.run("?- open('/etc/passwd', write, S).")
    assert r.verdict is Verdict.ERROR and "Permission denied" in r.output
    assert prolog.run("p(1).\n?- p(X).").verdict is Verdict.SAT  # the server survived


# -- clingo ---------------------------------------------------------------------------------


def test_clingo_errors_keep_their_context():
    clingo = need("clingo")
    r = clingo.run("p(X) :- not q(X).")
    assert r.verdict is Verdict.ERROR and "unsafe variables" in r.output and "'X' is unsafe" in r.output
    assert "Traceback" not in r.output


def test_clingo_rejects_embedded_scripts():
    clingo = need("clingo")
    r = clingo.run("#script (python)\nimport os\ndef main(prg):\n    os.system('id')\n#end.")
    assert r.verdict is Verdict.ERROR and "#script" in r.output


def test_clingo_timeout_is_flagged():
    clingo = need("clingo")
    r = clingo.run("p(1..100000000).", timeout=3)
    assert r.verdict is Verdict.UNKNOWN and r.details.get("timeout") and "time limit" in r.output


# -- idp ------------------------------------------------------------------------------------

IDP_V = "vocabulary V { c: () -> Int }\n"


def _idp_opt(idp, theory, op):
    return idp.run(IDP_V + f"theory T:V {{ {theory} }}\nprocedure main() {{ pretty_print({op}(T, term=\"c()\")) }}")


def test_idp_unbounded_objective_is_not_reported_optimal():
    idp = need("idp")
    r = _idp_opt(idp, "c() < 10.", "minimize")  # IDP-Z3 itself would claim c = -10 is optimal
    assert r.verdict is Verdict.SAT and r.details.get("unbounded") and "not proven" in r.output
    assert _idp_opt(idp, "c() < 10.", "maximize").verdict is Verdict.OPTIMAL
    bounded = _idp_opt(idp, "c() < 10. c() > -1000.", "minimize")
    assert bounded.verdict is Verdict.OPTIMAL and "-999" in bounded.output


def test_idp_clear_errors_for_empty_input_and_missing_main():
    idp = need("idp")
    assert "empty input" in idp.run("").output
    r = idp.run(IDP_V + "theory T:V { c() > 1. }")
    assert r.verdict is Verdict.ERROR and "procedure main()" in r.output


# -- mace4 -----------------------------------------------------------------------------------

NONCOMMUTATIVE_GROUP = """formulas(assumptions).
  (x * y) * z = x * (y * z).
  e * x = x.
  i(x) * x = e.
  exists u exists v (u * v != v * u).
end_of_list.
"""


def test_mace4_exhausted_search_without_goals_is_unsat_over_the_sizes():
    mace4 = need("mace4")
    r = mace4.run("assign(domain_size, 4).\n" + NONCOMMUTATIVE_GROUP)
    assert r.verdict is Verdict.UNSAT and r.details["sizes"] == [4] and "size 4 exists (exhaustive)" in r.output
    r = mace4.run("assign(start_size, 2).\nassign(end_size, 5).\n" + NONCOMMUTATIVE_GROUP)
    assert r.verdict is Verdict.UNSAT and r.details["sizes"] == [2, 3, 4, 5] and "2..5" in r.output
    r = mace4.run("assign(domain_size, 6).\n" + NONCOMMUTATIVE_GROUP)  # S3 has order 6
    assert r.verdict is Verdict.SAT and r.model


def test_mace4_exhausted_search_with_goals_stays_unknown():
    mace4 = need("mace4")
    code = ("assign(end_size, 5).\nformulas(assumptions).\n  e * x = x.\n  i(x) * x = e.\n  (x * y) * z = x * (y * z).\n"
            "  x * x = e.\nend_of_list.\nformulas(goals).\n  x * y = y * x.\nend_of_list.\n")  # fmt: skip
    r = mace4.run(code)
    assert r.verdict is Verdict.UNKNOWN and r.details["sizes"] == [2, 3, 4, 5] and "does not prove" in r.output


def test_mace4_without_end_size_hits_the_time_limit():
    mace4 = need("mace4")
    r = mace4.run(NONCOMMUTATIVE_GROUP.replace("exists u exists v (u * v != v * u).", "x * y = y * x.\n  "
                                                "exists u exists v (u * v != v * u)."), timeout=4)  # fmt: skip
    assert r.verdict is Verdict.UNKNOWN


# -- vampire ---------------------------------------------------------------------------------


def test_vampire_rejects_several_conjectures():
    vampire = need("vampire")
    r = vampire.run("fof(a, axiom, p).\nfof(c1, conjecture, q).\nfof(c2, conjecture, p).")  # Vampire alone: "proved"
    assert r.verdict is Verdict.ERROR and "DISJUNCTION" in r.output
    assert vampire.run("fof(a, axiom, p).\nfof(c, conjecture, (q & p)).").verdict is Verdict.REFUTED
    # one conjecture plus another in a comment is fine
    assert vampire.run("% fof(x, conjecture, q).\nfof(a, axiom, p).\nfof(c, conjecture, p).").verdict is Verdict.PROVED


def test_vampire_rejects_includes():
    vampire = need("vampire")
    for path in ("Axioms/SET001-0.ax", "/etc/passwd"):
        r = vampire.run(f"include('{path}').\nfof(c, conjecture, p).")
        assert r.verdict is Verdict.ERROR and "include() is not supported" in r.output and "root" not in r.output


def test_vampire_flags_vacuous_proofs():
    vampire = need("vampire")
    r = vampire.run("fof(a, axiom, p).\nfof(b, axiom, ~p).\nfof(c, conjecture, q).")
    assert r.verdict is Verdict.PROVED and r.details["vacuous"] and "inconsistent" in r.output
    assert "vacuous" not in vampire.run("fof(a, axiom, p).\nfof(c, conjecture, p).").details


def test_mace4_respects_the_time_limit_without_an_end_size():
    import time

    mace4 = need("mace4")
    start = time.monotonic()
    r = mace4.run("formulas(assumptions).\n  p.\n  -p.\nend_of_list.\n", timeout=4)  # mace4 alone never stops
    assert time.monotonic() - start < 10
    assert r.verdict is Verdict.UNKNOWN and r.details["timeout"] and r.details["sizes"][0] == 2


# -- one input for prover9 and mace4 -----------------------------------------------------------

BOTH = ("set(auto2).\nassign(max_models, 1).\nassign(end_size, 4).\nformulas(assumptions).\n  man(socrates).\n"
        "end_of_list.\nformulas(goals).\n  mortal(socrates).\nend_of_list.\n")  # fmt: skip


def test_prover9_ignores_mace4_options_and_says_so():
    prover9 = need("prover9")
    r = prover9.run(BOTH)
    assert r.verdict is Verdict.UNKNOWN and r.details["ignored"] == ["assign(max_models,1).", "assign(end_size,4)."]
    assert "ignored options" in r.output
    assert prover9.run("assign(max_secnds, 3).\nformulas(goals).\n  p | -p.\nend_of_list.").details["ignored"]


def test_mace4_ignores_prover9_options():
    mace4 = need("mace4")
    assert mace4.run(BOTH).verdict is Verdict.REFUTED


def test_portfolio_prover9_mace4_decides_both_ways():
    from formalkit import portfolio

    both = portfolio(need("prover9"), need("mace4"))
    refuted = both.run(BOTH, timeout=20)
    assert refuted.verdict is Verdict.REFUTED and refuted.backend == "mace4"
    proved = both.run(BOTH.replace("  man(socrates).", "  man(socrates).\n  man(x) -> mortal(x)."), timeout=20)
    assert proved.verdict is Verdict.PROVED and proved.backend == "prover9"


# -- downward --------------------------------------------------------------------------------

GRIP_D = """(define (domain gripper)
 (:requirements :strips :typing)
 (:types room ball gripper)
 (:predicates (at-robby ?r - room) (at ?b - ball ?r - room) (free ?g - gripper) (carry ?b - ball ?g - gripper))
 (:action move :parameters (?from ?to - room) :precondition (at-robby ?from)
   :effect (and (at-robby ?to) (not (at-robby ?from))))
 (:action pick :parameters (?b - ball ?r - room ?g - gripper) :precondition (and (at ?b ?r) (at-robby ?r) (free ?g))
   :effect (and (carry ?b ?g) (not (at ?b ?r)) (not (free ?g))))
 (:action drop :parameters (?b - ball ?r - room ?g - gripper) :precondition (and (carry ?b ?g) (at-robby ?r))
   :effect (and (at ?b ?r) (free ?g) (not (carry ?b ?g)))))"""
GRIP_P = """(define (problem g1) (:domain gripper)
 (:objects rooma roomb - room b1 b2 - ball left right - gripper)
 (:init (at-robby rooma) (free left) (free right) (at b1 rooma) (at b2 rooma))
 (:goal (and (at b1 roomb) (at b2 roomb))))"""


def test_downward_typo_in_objects_is_not_reported_unsolvable():
    dw = need("downward")
    r = dw.run(GRIP_D, problem=GRIP_P.replace("(at b2 rooma))", "(at b3 rooma))"))
    assert r.verdict is Verdict.ERROR and "undeclared object: b3" in r.output
    no_grippers = GRIP_P.replace("(free left) (free right) ", "")
    assert dw.run(GRIP_D, problem=no_grippers).verdict is Verdict.UNSAT  # genuinely unsolvable


def test_downward_accepts_common_plan_formats():
    dw = need("downward")
    steps = ["pick b1 rooma left", "pick b2 rooma right", "move rooma roomb", "drop b1 roomb left", "drop b2 roomb right"]
    for plan in ("\n".join(steps), "\n".join(f"{i}: ({s})" for i, s in enumerate(steps)),
                 "\n".join(f"({s.upper()})" for s in steps) + "\n; cost = 5 (unit cost)"):  # fmt: skip
        assert dw.run(GRIP_D, problem=GRIP_P, plan=plan).verdict is Verdict.PROVED, plan


def test_downward_clear_errors():
    dw = need("downward")
    assert "empty domain" in dw.run("", problem=GRIP_P).output
    cond_d = """(define (domain c) (:requirements :strips :conditional-effects) (:predicates (a) (g))
     (:action act :parameters () :precondition () :effect (and (a) (when (a) (g)))))"""
    r = dw.run(cond_d, problem="(define (problem c1) (:domain c) (:init) (:goal (g)))", mode="optimal")
    assert r.verdict is Verdict.ERROR and "does not support conditional effects" in r.output
    assert "Translator" not in r.output


# -- spin -----------------------------------------------------------------------------------


def test_spin_never_claims_are_checked():
    spin = need("spin")
    r = spin.run("byte x = 0;\nactive proctype A() { x = 1; x = 2 }\n"
                 "never { do :: x == 2 -> break :: else od; accept: do :: true od }")  # fmt: skip
    assert r.verdict is Verdict.REFUTED and r.details["properties"]["never claim"] == "violated"


def test_spin_deadlocks_are_checked_even_with_ltl_properties():
    spin = need("spin")
    r = spin.run("chan c = [0] of {bit};\nbyte x = 0;\nactive proctype A() { x = 1; c?1 }\nltl ok { [] (x <= 1) }")
    assert r.verdict is Verdict.REFUTED and "invalid end state" in r.output
    assert r.details["properties"] == {"safety (assertions, invalid end states)": "violated"}
    ok = spin.run("chan c = [0] of {bit};\nbyte x = 0;\nactive proctype A() { x = 1; end: c?1 }\nltl ok { [] (x <= 1) }")
    assert ok.verdict is Verdict.PROVED and ok.details["properties"]["ok"] == "holds"


def test_spin_ltl_violation_is_attributed_to_its_property():
    spin = need("spin")
    r = spin.run("byte cs = 0;\nactive proctype A() { cs = 1; cs = 0 }\nltl fine { [] (cs <= 1) }\nltl bad { [] (cs == 0) }")
    assert r.verdict is Verdict.REFUTED
    assert r.details["properties"] == {"safety (assertions, invalid end states)": "holds", "fine": "holds", "bad": "violated"}


# -- ddar ------------------------------------------------------------------------------------


def test_ddar_unknown_goal_predicate_is_an_error_not_a_refutation():
    ddar = need("ddar")
    r = ddar.run("a b c = triangle a b c ? foo a b c")
    assert r.verdict is Verdict.ERROR and "unknown goal predicate 'foo'" in r.output
    assert ddar.run("a b c = triangle a b c ? perp a b c").verdict is Verdict.ERROR  # perp takes 4 points


def test_ddar_rejects_redefined_points_and_empty_goals():
    ddar = need("ddar")
    assert "defined twice" in ddar.run("a b c = triangle a b c; a = midpoint a b c ? cong a b a c").output
    assert "empty goal" in ddar.run("a b c = triangle a b c ? ").output
    assert "empty problem" in ddar.run("   ").output


def test_ddar_tolerates_whitespace_and_hides_tracebacks():
    ddar = need("ddar")
    assert ddar.run("a b c = triangle a b c ;  d = midpoint d a b   ?   cong a d b d").verdict is Verdict.PROVED
    r = ddar.run("a b c = triangle a b; d = midpoint d a b ? cong a d b d")
    assert r.verdict is Verdict.ERROR and "triangle takes 3 points" in r.output and "Traceback" not in r.output


def test_clingo_counts_all_answer_sets():
    clingo = need("clingo")
    q8 = ("row(1..8). col(1..8).\n1 { q(R,C) : col(C) } 1 :- row(R).\n:- q(R1,C), q(R2,C), R1 < R2.\n"
          ":- q(R1,C1), q(R2,C2), R1 < R2, R1 - C1 == R2 - C2.\n:- q(R1,C1), q(R2,C2), R1 < R2, R1 + C1 == R2 + C2.\n#show q/2.")  # fmt: skip
    r = clingo.run(q8, timeout=30)
    assert r.details["count"] == 92 and r.details["count_complete"] and "92 answer sets in total" in r.output
    big = clingo.run("{p(1..40)}.", timeout=5)
    assert big.details["count_complete"] is False and "at least" in big.output


def test_clingo_show_projects_duplicate_solutions():
    clingo = need("clingo")
    r = clingo.run("{p(1..3)}. q :- p(1). #show q/0.")
    assert sorted(map(tuple, r.model)) == [(), ("q",)] and not r.details["more"]


# -- synthesize patterns ------------------------------------------------------------------------


def test_ask_with_feedback_bounds_the_prompt():
    from types import SimpleNamespace

    from formalkit import LLM, Result
    from formalkit.agent import Step
    from formalkit.patterns import ask_with_feedback

    seen = []

    def create(**kw):
        seen.append(kw["messages"][-1]["content"])
        return {"choices": [{"message": {"role": "assistant", "content": "```\nnext\n```"}}], "usage": {}}

    client = SimpleNamespace(chat=SimpleNamespace(completions=SimpleNamespace(create=create)))
    history = [Step("b", {"code": f"cand-{i}"}, Result(Verdict.REFUTED, f"fails-{i}")) for i in range(1, 11)]
    assert ask_with_feedback(LLM(client, "m"), "Task.", keep=3)(history) == "next"
    prompt = seen[-1]
    assert "(7 earlier attempts omitted" in prompt and "Attempt 8:" in prompt and "cand-10" in prompt
    assert "cand-7" not in prompt


# -- problog ---------------------------------------------------------------------------------


def test_problog_printed_text_is_not_a_probability():
    problog = need("problog")
    r = problog.run(":- writenl('count: 5').\n0.3::rain.\nquery(rain).")
    assert r.model == {"rain": 0.3} and "count: 5" in r.output


def test_problog_verdicts():
    problog = need("problog")
    assert problog.run("0.3::rain.\nevidence(rain, true).\nevidence(rain, false).\nquery(rain).").verdict is Verdict.UNSAT
    assert problog.run("query(foo).").verdict is Verdict.ERROR
    r = problog.run("n(0).\nn(X) :- n(Y), X is Y+1.\nquery(n(5)).", timeout=4)
    assert r.verdict is Verdict.UNKNOWN and "time limit" in r.output


def test_ddar_proof_uses_the_users_point_names():
    ddar = need("ddar")
    r = ddar.run("a b c = triangle a b c; h = on_tline h b a c, on_tline h c a b; d = foot d b a c ? perp a h b c")
    assert r.verdict is Verdict.PROVED and "BH ⟂ AC" in r.proof and "CH ⟂ AB" in r.proof


def test_synthesis_loops_do_not_rerun_repeated_candidates():
    from formalkit import Result
    from formalkit.patterns import cegis, propose_until_proved

    calls = []

    def verify(c):
        calls.append(c)
        return Result(Verdict.PROVED if c == "good" else Verdict.REFUTED, backend="v")

    proposals = iter(["bad", "bad", "bad", "good"])
    loop = cegis(lambda h: next(proposals), verify, rounds=5)
    assert loop.candidate == "good" and calls == ["bad", "good"] and len(loop.steps) == 4

    class Engine:
        name = "eng"
        runs = []

        def run(self, code, timeout=30, **kw):
            self.runs.append(code)
            return Result(Verdict.PROVED if "aux" in code else Verdict.UNKNOWN, backend="eng")

    engine = Engine()
    tries = iter(["p", "p", "p aux"])
    loop = propose_until_proved(engine, "p", lambda h: next(tries), rounds=4)
    assert loop.ok and engine.runs == ["p", "p aux"]


def test_prolog_accepts_not_as_a_prefix_operator():
    prolog = need("prolog")
    r = prolog.run("man(john).\nman(bill).\nmarried(john).\nbachelor(X) :- man(X), not married(X).\n?- bachelor(X).")
    assert r.verdict is Verdict.SAT and r.model["bachelor(X)"] == [{"X": "bill"}]
    assert prolog.run("p(1).\n?- not(p(1)).").verdict is Verdict.UNSAT


def test_ddar_checks_construction_arity_against_defs():
    ddar = need("ddar")
    r = ddar.run("a c b = triangle a c b; m = midpoint m a c; d = reflect d b m ? para a b c d")
    assert r.verdict is Verdict.ERROR and "reflect takes 4 points (reflect x a b c), got 3" in r.output
    assert "unknown construction 'frobnicate'" in ddar.run("a b c = triangle a b c; d = frobnicate d a b ? cong a d b d").output


def test_idp_accepts_percent_line_comments_and_keeps_modulo():
    idp = need("idp")
    r = idp.run("vocabulary V { x: () -> Int }\ntheory T:V {\n  % a comment\n  x() % 2 = 1.\n  x() > 4. x() < 7.\n}\n"
                "procedure main() { pretty_print(model_expand(T)) }")  # fmt: skip
    assert r.verdict is Verdict.SAT and "x := 5" in r.output


def test_downward_explains_unsupported_temporal_and_numeric_pddl():
    dw = need("downward")
    dur = """(define (domain d) (:requirements :durative-actions) (:predicates (p) (g))
     (:durative-action a :parameters () :duration (= ?duration 2) :condition (at start (p)) :effect (at end (g))))"""
    r = dw.run(dur, problem="(define (problem dp) (:domain d) (:init (p)) (:goal (g)))")
    assert r.verdict is Verdict.ERROR and "classical planner" in r.output


def test_clingo_interrupted_optimization_is_sat_with_timeout():
    clingo = need("clingo")
    r = clingo.run("{x(1..60)}.\n#maximize { X*Y,X,Y : x(X), x(Y), X != Y }.\n:- #count { X : x(X) } > 40.", timeout=4)
    assert r.verdict is Verdict.SAT and r.details.get("timeout") and "optimality not proven" in r.output
    assert clingo.run("{x(1..3)}.\n#minimize { 1,X : x(X) }.").verdict is Verdict.OPTIMAL


def test_vampire_question_answers_are_kept():
    vampire = need("vampire")
    r = vampire.run("fof(a1, axiom, parent(tom, bob)).\nfof(a2, axiom, parent(bob, ann)).\n"
                    "fof(gp, axiom, ![X,Y,Z]: ((parent(X,Y) & parent(Y,Z)) => grandparent(X,Z))).\n"
                    "fof(q, question, ?[W]: grandparent(tom, W)).")  # fmt: skip
    assert r.verdict is Verdict.PROVED and "W:=ann" in r.details["answers"] and "SZS answers" in r.output


def test_downward_refutations_are_structured():
    dw = need("downward")
    r = dw.run(GRIP_D, problem=GRIP_P, plan="(pick b1 rooma left)\n(move rooma roomb)\n(pick b2 rooma right)")
    ce = r.counterexample
    assert r.verdict is Verdict.REFUTED and ce["failed_step"] == 3 and ce["action"] == "(pick b2 rooma right)"
    assert ce["unsatisfied"] == ["(at-robby rooma)"] and "Repair Advice" in ce["report"]
    r = dw.run(GRIP_D, problem=GRIP_P, plan="(pick b1 rooma left)\n(move rooma roomb)\n(drop b1 roomb left)")
    assert r.verdict is Verdict.REFUTED and r.counterexample["unmet_goals"] == ["(at b2 roomb)"]


def test_downward_names_malformed_plan_steps():
    dw = need("downward")
    r = dw.run(GRIP_D, problem=GRIP_P, plan="(fly b1)\n(pick b1 rooma)")
    assert r.verdict is Verdict.REFUTED and "unknown action 'fly'" in r.output and "pick takes 3 argument(s)" in r.output


def test_mace4_refutes_a_set_of_goals_where_one_is_false():
    mace4 = need("mace4")
    code = "assign(end_size, 4).\nformulas(assumptions).\n  p(a).\nend_of_list.\nformulas(goals).\n  p(a).\n  q(a).\nend_of_list."
    r = mace4.run(code)  # mace4 alone: unknown (it looks for a model falsifying BOTH goals)
    assert r.verdict is Verdict.REFUTED and r.details["goals_conjoined"] and "one conjunction" in r.output
    from formalkit import portfolio

    assert portfolio(need("prover9"), mace4).run(code).verdict is Verdict.REFUTED


def test_downward_accepts_domain_and_problem_together_in_code():
    dw = need("downward")
    r = dw.run(GRIP_D + "\n\n" + GRIP_P)  # e.g. what refine/translate_and_solve send: one code block
    assert r.verdict is Verdict.SAT and len(r.model) == 5
    assert "missing `problem`" in dw.run(GRIP_D).output


def test_prolog_queries_share_the_time_budget():
    import time

    prolog = need("prolog")
    start = time.monotonic()
    r = prolog.run("loop :- loop.\np(1).\n?- p(X).\n?- loop.\n?- loop.\n?- p(Y).", timeout=6)
    assert time.monotonic() - start < 10
    assert r.verdict is Verdict.UNKNOWN and [q["status"] for q in r.details["queries"]] == [True, "timeout", "timeout", True]


def test_mace4_conjoined_goals_drop_attributes():
    mace4 = need("mace4")
    r = mace4.run("assign(end_size, 4).\nformulas(assumptions).\n  p(a).\nend_of_list.\nformulas(goals).\n"
                  "  p(a) # label(g1).\n  q(a) # label(g2).\nend_of_list.")  # fmt: skip
    assert r.verdict is Verdict.REFUTED


def test_spin_ltl_without_space_is_checked():
    spin = need("spin")
    r = spin.run("byte x = 0;\nactive proctype A() { x = 1 }\nltl{ [] (x == 0) }")
    assert r.verdict is Verdict.REFUTED and r.details["properties"]["ltl_0"] == "violated"


def test_prolog_closed_world_for_undefined_body_predicates():
    prolog = need("prolog")
    r = prolog.run("jompus(X) :- tumpus(X).\nbright(X) :- jompus(X).\nzumpus(stella).\n?- bright(stella).")
    assert r.verdict is Verdict.UNSAT and r.details["closed_world"] == ["tumpus/1"]
    assert prolog.run("p(1).\n?- pp(1).").verdict is Verdict.ERROR  # a never-mentioned predicate: likely a typo
    assert prolog.run("in(X) :- member(X, [1,2,3]).\n?- in(2).").verdict is Verdict.SAT  # libraries untouched


def test_spin_unnamed_claims_are_numbered_among_themselves():
    spin = need("spin")
    r = spin.run("byte x = 0;\nactive proctype A() { x = 1 }\nltl named { [] (x <= 1) }\nltl { [] (x == 0) }")
    assert r.verdict is Verdict.REFUTED and r.details["properties"]["ltl_0"] == "violated"


def test_ddar_cyclic_goals_are_checked_numerically():  # upstream check_cyclic crashed on every cyclic goal
    ddar = need("ddar")
    r = ddar.run("a b c = triangle a b c; o = circle o a b c; h = midpoint h c b; d = on_line d o h, on_line d a b; "
                 "e = on_tline e c c o, on_tline e a a o ? cyclic a o e d")  # fmt: skip
    assert r.verdict is Verdict.PROVED


def test_ddar_configuration_dependent_theorem_is_not_refuted():
    ddar = need("ddar")
    p = ("a b c d = isquare a b c d; e = midpoint e b a; f = on_line f a b; "
         "g = on_tline g e d e, angle_bisector g c b f ? cong d e e g")  # true for some placements of f only
    assert {ddar.run(p, timeout=60).verdict for _ in range(4)} == {Verdict.PROVED}


def test_mace4_goal_search_is_bounded_by_default():
    import time

    mace4 = need("mace4")
    start = time.monotonic()
    r = mace4.run("formulas(assumptions).\n  tv(westworld).\nend_of_list.\nformulas(goals).\n  exists x tv(x).\nend_of_list.",
                  timeout=30)  # fmt: skip
    assert time.monotonic() - start < 10 and r.verdict is Verdict.UNKNOWN and r.details["default_end_size"] == 40


def test_vampire_rejects_a_question_next_to_a_conjecture():
    vampire = need("vampire")
    r = vampire.run("fof(a, axiom, p(a)).\nfof(c, conjecture, q(a)).\nfof(q2, question, ?[X]: p(X)).")
    assert r.verdict is Verdict.ERROR and "DISJUNCTION" in r.output


def test_one_second_budgets_never_crash():
    cases = {
        "vampire": ("fof(a,axiom,p).\nfof(c,conjecture,p).", {}),
        "spin": ("int a, b;\nactive proctype A() { do :: a = (a + 1) % 30000 :: b = (b + 7) % 30001 od }", {}),
        "prolog": ("loop :- loop.\n?- loop.", {}),
        "clingo": ("p(1..100000000).", {}),
        "mace4": ("formulas(assumptions).\n  p.\n  -p.\nend_of_list.", {}),
    }
    for name, (code, kw) in cases.items():
        r = need(name).run(code, timeout=1, **kw)
        assert r.verdict in (Verdict.UNKNOWN, Verdict.PROVED), (name, r.output)
        assert "internal" not in r.output and r.output.strip(), name


def test_vampire_input_without_formulas_is_an_error():
    vampire = need("vampire")
    for code in ("", "% only a comment", "\x00\x00abc\x00"):
        r = vampire.run(code)
        assert r.verdict is Verdict.ERROR and "no TPTP formulas" in r.output


def test_vampire_never_proves_false_integer_arithmetic_under_load():
    """Vampire 5.1.0's uwa=alasca_main strategies 'proved' this false conjecture (under load, 6/8 runs)."""
    from concurrent.futures import ThreadPoolExecutor

    vampire = need("vampire")
    false_conjecture = "tff(c, conjecture, ![X: $int, Y: $int]: (0 = $difference(5, $sum(X, 4))))."
    with ThreadPoolExecutor(8) as pool:
        verdicts = list(pool.map(lambda _: vampire.run(false_conjecture, timeout=15).verdict, range(8)))
    assert Verdict.PROVED not in verdicts
    assert vampire.run("tff(c, conjecture, ![X: $int]: $less(X, $sum(X, 1))).").verdict is Verdict.PROVED


def test_prolog_closed_world_leaves_library_expansions_alone():
    prolog = need("prolog")
    r = prolog.run(":- use_module(library(clpfd)).\np(X, Y) :- X + Y #= 10, X #> Y, [X, Y] ins 0..10, label([X, Y]).\n"
                   "?- p(X, Y).")  # fmt: skip
    assert r.verdict is Verdict.SAT and "closed_world" not in r.details


def test_problog_rejects_disjunctions_summing_past_one():
    problog = need("problog")
    r = problog.run("0.7::a; 0.6::b.\nquery(a).")  # ProbLog itself only notices when b is relevant to a query
    assert r.verdict is Verdict.ERROR and "sum 1.3" in r.output
    assert problog.run("0.2::red; 0.3::green; 0.5::blue.\nquery(red).").verdict is Verdict.SAT


def test_downward_names_arity_errors_and_unbound_variables():
    dw = need("downward")
    r = dw.run(GRIP_D, problem=GRIP_P.replace("(at b2 rooma))", "(at b2))"))
    assert r.verdict is Verdict.ERROR and "at takes 2 argument(s), got 1" in r.output and "b'Traceback" not in r.output
    d = GRIP_D.replace("(:action move :parameters (?from ?to - room) :precondition (at-robby ?from)",
                       "(:action move :parameters (?from - room) :precondition (at-robby ?from)")
    r = dw.run(d, problem=GRIP_P)
    assert r.verdict is Verdict.ERROR and "not in its :parameters" in r.output and "b'Traceback" not in r.output


def test_prover9_verdict_comes_from_the_proofs_not_the_exit_code():
    prover9 = need("prover9")
    # Horn set with several negative clauses: auto mode raises max_proofs and exits "sos empty" after the proof
    horn = ("formulas(assumptions).\n  red != amber.\n  amber != green.\n  red != green.\n"
            "  all x (complete(x) <-> (reached(x,red) & reached(x,amber) & reached(x,green))).\nend_of_list.\n"
            "formulas(goals).\n  all x (complete(x) -> reached(x,green)).\nend_of_list.")  # fmt: skip
    assert prover9.run(horn).verdict is Verdict.PROVED
    r = prover9.run("formulas(assumptions).\n  p.\n  -p.\nend_of_list.\nformulas(goals).\n  q.\nend_of_list.")
    assert r.verdict is Verdict.PROVED and r.details["vacuous"] and "contradictory" in r.output
    r = prover9.run("formulas(assumptions).\n  p.\n  -p.\nend_of_list.")
    assert r.verdict is Verdict.UNSAT and "vacuous" not in r.details
    r = prover9.run("formulas(assumptions).\n  p.\nend_of_list.\nformulas(goals).\n  p.\n  q.\nend_of_list.")
    assert r.verdict is Verdict.UNKNOWN and "1 of 2 goals" in r.output


def test_ddar_accepts_alphageometry_shorthand_syntax():
    ddar = need("ddar")
    # implicit construction arguments and fixed coordinates, as in AlphaGeometry's imo_ag_30.txt
    r = ddar.run("a b c = triangle; d = midpoint a b; e = midpoint a c ? para d e b c")
    assert r.verdict is Verdict.PROVED, r.output
    r = ddar.run("x@0.0_0.0 y@1.0_0.0 z@0.3_0.8 = triangle x y z; m = midpoint m x y ? cong m x m y")
    assert r.verdict is Verdict.PROVED, r.output


def test_ddar_does_not_refute_when_coordinates_are_fixed():
    ddar = need("ddar")
    r = ddar.run("x@0.0_0.0 y@1.0_0.0 z@0.3_0.8 = triangle x y z ? perp x y x z")
    assert r.verdict is Verdict.UNKNOWN and "no refutation claimed" in r.output


def test_spin_deepens_the_search_when_runs_are_long():
    spin = need("spin")
    code = "int x = 0;\nactive proctype A() { do :: x < 150000 -> x++ :: else -> break od; assert(x == 150000) }"
    assert spin.run(code, timeout=60).verdict is Verdict.PROVED  # needs more than the initial 100000-step depth
