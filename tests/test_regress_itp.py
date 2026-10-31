"""Regressions found by real-world testing of the ITP backends and proof patterns (Docker)."""

from __future__ import annotations

import pytest

from formalkit import Verdict, backend, docker

pytestmark = pytest.mark.docker


@pytest.fixture(scope="module")
def lean():
    if not docker.has_image("lean"):
        pytest.skip("lean image not built")
    return backend("lean")


FORGED_FALSE = """import Lean
open Lean Elab Command in
set_option debug.skipKernelTC true in
run_cmd liftCoreM <| addDecl (Declaration.thmDecl
  { name := `evil, levelParams := [], type := mkConst ``False, value := mkConst ``True.intro })
theorem t : False := evil
"""


@pytest.mark.parametrize(
    "code,verdict,why",
    [
        # Trusting compiled code instead of the kernel.
        ("theorem t : 2^10 = 1024 := by native_decide", Verdict.ERROR, "native_decide"),
        ("theorem t : 2^5 = 32 := by decide +native", Verdict.ERROR, "native_decide"),
        ("example : 2^10 = 1024 := by native_decide", Verdict.ERROR, "native_decide"),
        # Everything after #exit goes unchecked.
        ("theorem t : 1 = 1 := rfl\n#exit\ntheorem u : 1 = 2 := by simp", Verdict.ERROR, "#exit"),
        # Nothing stated, nothing proved.
        ("", Verdict.UNKNOWN, "nothing was proved"),
        ("-- just a comment", Verdict.UNKNOWN, "nothing was proved"),
        ("def x : Nat := 3", Verdict.UNKNOWN, "nothing was proved"),
        # Holes in disguise stay holes.
        ("theorem t (n : Nat) : n = n + 0 := by admit", Verdict.UNKNOWN, "sorry"),
        ('macro "mytac" : tactic => `(tactic| sorry)\ntheorem t : 1 = 2 := by mytac', Verdict.UNKNOWN, "sorry"),
        ("axiom bad : False\ntheorem t : 1 = 2 := bad.elim", Verdict.ERROR, "axiom"),
    ],
)
def test_lean_soundness(lean, code, verdict, why):
    result = lean.run(code, timeout=120)
    assert result.verdict is verdict, result.feedback()
    assert why in result.output


def test_lean_forged_false_is_never_proved(lean):
    # Bypassing the kernel while elaborating. Stopped by the code-execution rule, and - should
    # that ever be evaded - by the independent kernel replay.
    result = lean.run(FORGED_FALSE, timeout=120)
    assert result.verdict is not Verdict.PROVED, result.feedback()


@pytest.mark.parametrize(
    "code",
    [
        "-- sorry in a comment\ntheorem t : 1 = 1 := rfl /- sorry -/",
        'def s := "sorry"\ntheorem t : 1 = 1 := rfl',
        "theorem sorry_free : 1 = 1 := rfl",
        "namespace Foo\nprivate theorem p : 2 = 2 := rfl\nend Foo\nexample : 3 = 3 := rfl",
        # A harmless use of the option: the replay re-checks everything anyway.
        "set_option debug.skipKernelTC true in\ntheorem t : 1 = 1 := rfl",
    ],
)
def test_lean_no_false_alarms(lean, code):
    result = lean.run(code, timeout=120)
    assert result.verdict is Verdict.PROVED, result.feedback()


def test_lean_session_cannot_smuggle_native_decide(lean):
    root = lean.start("theorem t : 2^10 = 1024 := by\n  sorry")
    done = root.apply("native_decide")
    assert not done.solved and done.result.verdict is Verdict.ERROR


def _kill_repls():
    import subprocess

    subprocess.run(["docker", "exec", docker.container("lean"), "sh", "-c",
                    # match the executable path: this shell's own command line also mentions "repl"
                    "for p in /proc/[0-9]*; do case \"$(tr '\\0' ' ' < $p/cmdline 2>/dev/null)\" in "
                    "/opt/repl/*) kill -9 ${p#/proc/};; esac; done"],
                   check=False)  # fmt: skip


def test_lean_session_survives_a_dead_repl(lean):
    stale = lean.start("theorem t (n : Nat) : n + 0 = n := by\n  sorry")
    _kill_repls()
    after = stale.apply("simp")
    out = after.result.output
    assert after.failed and ("expired" in out or "stopped unexpectedly" in out)  # never a wrong answer
    fresh = lean.start("theorem t (n : Nat) : n + 0 = n := by\n  sorry")  # restarts transparently
    assert not fresh.failed and fresh.apply("simp").solved


def test_lean_sorry_goals_after_a_dead_repl(lean):
    lean.start("theorem t (n : Nat) : n + 0 = n := by\n  sorry")
    _kill_repls()
    result = lean.run("theorem t (n : Nat) : n + 0 = n := by\n  sorry")
    assert result.verdict is Verdict.UNKNOWN and result.goals == ["n : Nat\n⊢ n + 0 = n"]


# -- Isabelle ------------------------------------------------------------------------------


@pytest.fixture(scope="module")
def isabelle():
    if not docker.has_image("isabelle"):
        pytest.skip("isabelle image not built")
    return backend("isabelle")


def _thy(body, imports="Main"):
    return f"theory A imports {imports} begin\n{body}\nend\n"


@pytest.mark.parametrize(
    "body,verdict,why",
    [
        # ML can forge theorems (oracles, Skip_Proof.cheat_tac): rejected outright.
        ('lemma "1 = (2::nat)" by (tactic \\<open>Skip_Proof.cheat_tac \\<^context> 1\\<close>)', Verdict.ERROR, "ML-level"),
        ('method_setup cheat = \\<open>Scan.succeed (fn ctxt => SIMPLE_METHOD (Skip_Proof.cheat_tac ctxt 1))\\<close>\n'
         'lemma "1 = (2::nat)" by cheat', Verdict.ERROR, "ML-level"),
        ('ML \\<open>val x = 1\\<close>\nlemma "True" by simp', Verdict.ERROR, "ML-level"),
        # Several commands may share a line: the ban is token-based, not line-based.
        ('lemma "True" by simp ML \\<open>val x = 1\\<close>\nlemma "True" by simp', Verdict.ERROR, "ML-level"),
        ('lemma "True" by simp setup \\<open>I\\<close>', Verdict.ERROR, "ML-level"),
        # ...but command words inside names and terms are not commands.
        ('lemma setup_ok: "True" by simp\nlemma "(ML::nat) = ML" by simp', Verdict.PROVED, "theorem setup_ok"),
        # Nothing stated, nothing proved.
        ('definition f :: "nat \\<Rightarrow> nat" where "f x = x"', Verdict.UNKNOWN, "nothing was proved"),
        # Words in document text are not commands.
        ('text \\<open>sorry, we use no ML here\\<close>\nlemma "True" by simp', Verdict.PROVED, "theorem True"),
    ],
)
def test_isabelle_soundness(isabelle, body, verdict, why):
    result = isabelle.run(_thy(body), timeout=240)
    assert result.verdict is verdict, result.feedback()
    assert why in result.output


def test_isabelle_hol_library_imports(isabelle):
    result = isabelle.run(_thy('lemma "(2::int) ^ 10 = 1024" by simp', imports='Main "HOL-Library.Multiset"'), timeout=240)
    assert result.verdict is Verdict.PROVED, result.feedback()


def test_isabelle_concurrency_does_not_oom(isabelle):
    from concurrent.futures import ThreadPoolExecutor

    with ThreadPoolExecutor(6) as pool:
        results = list(pool.map(lambda i: isabelle.run(_thy(f'lemma "{i} + x = x + ({i}::nat)" by simp'), timeout=600),
                                range(6)))  # fmt: skip
    assert all(r.verdict is Verdict.PROVED for r in results), [r.output[-200:] for r in results]


# -- Metamath ------------------------------------------------------------------------------


@pytest.fixture(scope="module")
def metamath():
    if not docker.has_image("metamath"):
        pytest.skip("metamath image not built")
    return backend("metamath")


def test_metamath_rejects_new_syntax_on_setmm(metamath):
    result = metamath.run("$[ set.mm $]\n${ wevil $a wff ( ph -> ps ) $. $}\nmyid $p |- ( ph -> ph ) $= ( id ) AB $.")
    assert result.verdict is Verdict.ERROR and "wevil" in result.output


def test_metamath_no_trailing_newline_noise(metamath):
    result = metamath.run("$[ set.mm $]\nmyid $p |- ( ph -> ph ) $= ( id ) AB $.")
    assert result.verdict is Verdict.PROVED and "incomplete" not in result.output


@pytest.mark.parametrize(
    "code",
    [
        "#eval 2 + 2\ntheorem t : 1 = 1 := rfl",
        "set_option pp.all true in #eval 1\ntheorem t : 1 = 1 := rfl",
        "import Lean\ntheorem t : True := by run_tac pure ()\n  trivial",
        'import Lean\nopen Lean Elab Command in\nelab "noop" : command => pure ()\nnoop\ntheorem t : 1 = 1 := rfl',
    ],
)
def test_lean_compile_time_code_is_never_certified(lean, code):
    result = lean.run(code, timeout=120)
    assert result.verdict is not Verdict.PROVED, result.feedback()


def test_lean_session_step_running_code_is_not_certified(lean):
    root = lean.start("import Lean\ntheorem t : True := by\n  sorry")
    step = root.apply("run_tac pure ()\ntrivial")
    assert not step.solved


def test_lean_char_literal_does_not_hide_code_from_the_guards(lean):
    code = "def q : Char := '\"'\nexample : 2 ^ 10 = 1024 := by native_decide"
    assert lean.run(code, timeout=120).verdict is Verdict.ERROR


def test_isabelle_timeout_leaves_no_prover_running(isabelle):
    import subprocess
    import time

    looping = _thy('definition f :: "nat \\<Rightarrow> nat" where "f n = n"\nlemma fg: "f n = f (n + 0)" by simp\n'
                   'lemma "f x = x" by (simp only: fg)')  # fmt: skip
    assert isabelle.run(looping, timeout=20).verdict is Verdict.UNKNOWN
    time.sleep(3)
    ps = subprocess.run(["docker", "exec", docker.container("isabelle"), "ps", "-eo", "comm"],
                        capture_output=True, text=True).stdout.split()  # fmt: skip
    assert "poly" not in ps, ps
