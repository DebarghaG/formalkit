"""Shared SMT-LIB output classification (Z3, cvc5).

Ported from ProofOfThought's agentic executor, where it was hardened over
tens of thousands of trajectories: the verdict that counts is the *last*
``sat``/``unsat``/``unknown`` line; an error *before* it poisons it (the
solver checked a different encoding than the model wrote), while an error
after it - e.g. ``(get-model)`` after ``unsat`` - is harmless.
"""

from __future__ import annotations

import re

from formalkit.core import Result, Verdict

_VERDICTS = {"sat": Verdict.SAT, "unsat": Verdict.UNSAT, "unknown": Verdict.UNKNOWN}
# Solver errors are `(error "...")` lines (plus z3's bare `unsupported` and command-line `ERROR:`).
# Anything looser misfires on model values: a datatype constructor named `Error`, a value `(error 3)`.
# A failed *query* (get-model after unknown, get-unsat-core without a core...) changes nothing that a later
# (check-sat) decides, unlike a failed declaration or assertion; it must not poison the verdict.
_QUERY_ERROR = re.compile(
    r"not available|[Cc]annot get|can't get|unless (model|proof|unsat.core)|not enabled|interactive mode"
    r"|check annotation|Expected result",  # a (set-info :status ...) expectation that the answer contradicts
    re.I,
)
_ERROR_LINE = re.compile(r'^(\(error\s+"|unsupported\s*$|ERROR:|error:)')


def parse_sexprs(text: str) -> list:
    """Parse s-expressions into nested lists of atom strings; strings keep their quotes."""
    out: list = []
    stack: list[list] = [out]
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if c.isspace():
            i += 1
        elif c == ";":
            while i < n and text[i] != "\n":
                i += 1
        elif c == "(":
            stack.append([])
            i += 1
        elif c == ")":
            if len(stack) == 1:
                raise ValueError("unbalanced )")
            done = stack.pop()
            stack[-1].append(done)
            i += 1
        elif c == '"':
            j = i + 1
            while j < n and not (text[j] == '"' and text[j + 1 : j + 2] != '"'):
                j += 2 if text[j] == '"' else 1
            stack[-1].append(text[i : j + 1])
            i = j + 1
        elif c == "|":
            j = text.index("|", i + 1)
            stack[-1].append(text[i : j + 1])
            i = j + 1
        else:
            j = i
            while j < n and not text[j].isspace() and text[j] not in '();"|':
                j += 1
            stack[-1].append(text[i:j])
            i = j
    if len(stack) != 1:
        raise ValueError("unbalanced (")
    return out


def render(expr) -> str:
    return expr if isinstance(expr, str) else "(" + " ".join(render(e) for e in expr) + ")"


def parse_model(text: str) -> dict[str, str]:
    """``{name: value}`` from ``(get-model)`` output; functions become ``(lambda (args) body)``."""
    try:
        exprs = parse_sexprs(text)
    except (ValueError, IndexError):
        return {}
    model: dict[str, str] = {}

    def walk(e) -> None:
        if not isinstance(e, list):
            return
        if len(e) == 5 and e[0] == "define-fun" and isinstance(e[1], str):
            _, name, args, _sort, body = e
            model[name] = render(body) if not args else f"(lambda {render(args)} {render(body)})"
            return
        for sub in e:
            walk(sub)

    for e in exprs:
        walk(e)
    return model


def _forms_after(output: str, marker: str) -> list:
    """Parsed s-expressions printed after the last ``marker`` verdict line (unparsable text is skipped)."""
    lines = output.splitlines()
    last = max(i for i, line in enumerate(lines) if line.strip() == marker)
    forms = []
    for chunk in _balanced_chunks("\n".join(lines[last + 1 :])):
        try:
            forms += parse_sexprs(chunk)
        except (ValueError, IndexError):
            continue
    return forms


def _balanced_chunks(text: str) -> list:
    """Split text into top-level parenthesized chunks, tolerating junk between them."""
    chunks, depth, start, i, n = [], 0, None, 0, len(text)
    while i < n:
        c = text[i]
        if c == '"':  # skip string literals ("" is an escaped quote)
            i += 1
            while i < n and not (text[i] == '"' and text[i + 1 : i + 2] != '"'):
                i += 2 if text[i] == '"' else 1
        elif c == "|":
            j = text.find("|", i + 1)
            i = n if j < 0 else j
        elif c == "(":
            if depth == 0:
                start = i
            depth += 1
        elif c == ")" and depth:
            depth -= 1
            if depth == 0:
                chunks.append(text[start : i + 1])
        i += 1
    return chunks


def _unsat_core(output: str) -> "list[str] | None":
    """Names from ``(get-unsat-core)`` after the last ``unsat``: the assertions that conflict.

    Needs ``(set-option :produce-unsat-cores true)`` and ``(! ... :named n)``
    assertions in the script (or ``check-sat-assuming`` + ``get-unsat-assumptions``,
    whose literals may be negated); None when the script did not ask for a core.
    Works for one-line (z3) and multi-line (cvc5) printing.
    """
    for form in _forms_after(output, "unsat"):
        if not isinstance(form, list) or form[:1] == ["error"]:
            continue
        # names, or (with check-sat-assuming / get-unsat-assumptions) negated literals such as (not b)
        if all(isinstance(x, str) or (isinstance(x, list) and len(x) == 2 and x[0] == "not" and isinstance(x[1], str))
               for x in form):  # fmt: skip
            return [x.strip("|") if isinstance(x, str) else render(x) for x in form]
    return None


def _values_and_objectives(output: str) -> "tuple[dict, dict]":
    """``(get-value ...)`` pairs and z3 ``(objectives ...)`` printed after the last ``sat``."""
    values, objectives = {}, {}
    for form in _forms_after(output, "sat"):
        if not isinstance(form, list) or not form:
            continue
        if form[0] == "objectives":
            objectives.update({render(p[0]): render(p[1]) for p in form[1:] if isinstance(p, list) and len(p) == 2})
        elif all(isinstance(p, list) and len(p) == 2 for p in form):
            values.update({render(p[0]): render(p[1]) for p in form})
    return values, objectives


# Names models write from older SMT-LIB versions or other languages, and the SMT-LIB 2.6 spelling.
_RENAMED = {"str.to.re": "str.to_re", "str.in.re": "str.in_re", "str.to.int": "str.to_int", "int.to.str": "str.from_int",
            "str.to-int": "str.to_int", "int.to-str": "str.from_int", "re.nostr": "re.none", "iff": "=",
            "implies": "=>", "bv2int": "bv2nat"}  # fmt: skip
_LOGIC_RE = re.compile(r"\(\s*set-logic\s+([^\s()]+)\s*\)")


def hint(code: str, result: Result) -> Result:
    """Append a one-line hint for well-known traps whose solver message does not say what to fix."""
    out, logic = result.output, _LOGIC_RE.search(code)
    tip = None
    if "setLogicString" in out:
        tip = f"{logic.group(1) if logic else 'that'} is not an SMT-LIB logic; use (set-logic ALL) or omit set-logic"
    elif "Only one set-logic is allowed" in out and len(_LOGIC_RE.findall(code)) == 1:
        tip = "set-logic must come before any declaration (the logic is fixed at the first declaration)"
    elif "in a linear logic" in out or ("non-linear" in out and logic):
        tip = "the declared logic is linear; use a nonlinear logic such as QF_NIA / QF_NRA, or (set-logic ALL)"
    elif re.search(r"logic does not support ([\w -]+)", out):
        what = re.search(r"logic does not support ([\w -]+)", out).group(1).strip()
        tip = (f"{logic.group(1) if logic else 'the declared logic'} does not include {what}; "
               "use a logic that does (e.g. ALL) or omit set-logic")  # fmt: skip
    elif re.search(r"(constant|Symbol|function)\W+(max|min)\b", out):
        tip = "max / min are not SMT-LIB functions; write (ite (>= a b) a b) / (ite (<= a b) a b)"
    elif re.search(r"got `(maximize|minimize|get-objectives)`", out):
        tip = "maximize / minimize / get-objectives are z3 extensions; use the z3 backend for optimization"
    elif re.search(r"^unsupported\s*$", out, re.M) and re.search(r"\(\s*set-option\s+:timeout\b", code):
        tip = "this solver does not support (set-option :timeout ...); remove it (formalkit applies the time limit)"
    elif result.verdict is Verdict.UNKNOWN and logic and logic.group(1).upper() in ("HORN", "QF_FD"):
        tip = f"(set-logic {logic.group(1)}) selects a special-purpose engine; for ordinary assertions omit set-logic"
    if tip is None and result.verdict is Verdict.ERROR:
        for name, current in _RENAMED.items():
            if re.search(rf"(Symbol|constant|function)\W+{re.escape(name)}\b", out):
                tip = f"{name} is not SMT-LIB 2.6; use {current}"
                break
    if tip:
        result.output = f"{out}\nhint: {tip}"
    return result


def unfence(code: str) -> str:
    """The script inside a markdown code fence, if a model wrapped it in one (possibly after some prose).

    Text that already starts like a script (``(``, ``;``, DIMACS ``p``/``c``/digits) is left alone, so
    backticks inside comments never change a real script.
    """
    text = code.strip()
    if "```" not in text or (text[:1] in "(;pc-0123456789" and not text.startswith("```")):
        return code
    blocks = re.findall(r"```[^\n`]*\n(.*?)```", text, re.DOTALL)
    if blocks:
        return blocks[-1]
    body = text.split("```", 1)[1]  # an unclosed fence: everything after its first line
    return body.split("\n", 1)[1] if "\n" in body else ""


def classify(output: str, code: str = "") -> Result:
    verdicts: list[str] = []
    error_seen = error_before_last = False
    for raw in output.splitlines():
        line = raw.strip()
        if line in _VERDICTS:
            verdicts.append(line)
            error_before_last = error_seen
        elif _ERROR_LINE.match(line) and not _QUERY_ERROR.search(line):
            error_seen = True
    details = {"check_sat": verdicts}
    if not verdicts:
        msg = output if error_seen else (output + "\nno (check-sat) result in output").strip()
        return Result(Verdict.ERROR, msg, details)
    if error_before_last or error_seen:
        # Any failed declaration/assertion/command - before the verdict, or after it (e.g. a script cut
        # off mid-assertion, whose intended check never ran) - makes the run an error. Failed queries
        # such as (get-model) after unsat are not counted (see _QUERY_ERROR).
        return Result(Verdict.ERROR, output, details)
    verdict = _VERDICTS[verdicts[-1]]
    if verdicts[-1] == "sat":
        # The model printed after the last (check-sat), if the script asked for one;
        # (get-value ...) answers fill in when there is no (get-model).
        lines = output.splitlines()
        last = max(i for i, line in enumerate(lines) if line.strip() == "sat")
        model = parse_model("\n".join(lines[last + 1 :]))
        values, objectives = _values_and_objectives(output)
        for key, value in values.items():
            model.setdefault(key, value)
        if model:
            details["model"] = model
        if objectives:
            details["objectives"] = objectives
            # z3's optimizer answers sat with the optimum; unbounded or open objectives
            # (oo, epsilon) are not optima.
            if not any(re.search(r"\b(oo|epsilon|interval)\b", v) for v in objectives.values()):
                verdict = Verdict.OPTIMAL
    elif verdicts[-1] == "unsat":
        core = _unsat_core(output)
        if core is not None:
            details["core"] = core
        if re.search(r"\(\s*get-proof\b", code):  # the solver's proof object, as printed
            lines = output.splitlines()
            last = max(i for i, line in enumerate(lines) if line.strip() == "unsat")
            proof = "\n".join(line for line in lines[last + 1 :] if not _ERROR_LINE.match(line.strip())).strip()
            if proof:
                details["proof"] = proof
    if verdicts[-1] != "sat":
        # (get-model) after unsat/unknown only reports that there is no model: noise for a reader.
        output = "\n".join(line for line in output.splitlines() if "model is not available" not in line)
    return Result(verdict, output, details)
