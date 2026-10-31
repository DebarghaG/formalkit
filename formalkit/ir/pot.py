"""Proof of Thought's JSON DSL as a formalkit intermediate representation.

ProofOfThought (Ganguly et al., 2024) has the model write a JSON program -
sorts, functions, constants, a knowledge base, rules and one verification -
whose premise-and-rule structure is what gets verified. Here that DSL
becomes a *compiled* backend: the JSON is compiled to SMT-LIB 2.6 and run on
z3, so it composes with everything else (agent, MCP, patterns, recheck).

    pot = formalkit.backend("pot")
    pot.run(json_program).verdict          # sat / unsat, like ProofOfThought

Expressions use ProofOfThought's z3py-style syntax (``ForAll([x], Implies(
f(x), g(x)))``, ``a == b``, ``x + 1 > y``). They are parsed with Python's
``ast`` module and translated - never evaluated - so the compiler needs no
z3 and runs no model-written code. Type checking happens at compile time,
so the model gets precise errors ("f expects 2 arguments", "unknown symbol
'x'") instead of solver noise.

Semantics follow ProofOfThought exactly: the knowledge base and rules are
asserted; the verification is checked as an assumption (``KB ∧ condition``):
sat means the condition is consistent with the knowledge base, unsat that it
contradicts it. To prove that the KB *entails* a claim, verify the claim's
negation and look for unsat.
"""

from __future__ import annotations

import ast
import json
from decimal import Decimal
from typing import Any

from formalkit.llm import extract_code

BUILTIN = {"BoolSort": "Bool", "IntSort": "Int", "RealSort": "Real"}
_RESERVED = {
    "true", "false", "and", "or", "not", "ite", "let", "forall", "exists", "assert", "par", "match",
    "as", "distinct", "_", "!", "NUMERAL", "DECIMAL", "STRING", "BINARY", "HEXADECIMAL",
}  # fmt: skip
_NARY = {"And": "and", "Or": "or", "Distinct": "distinct"}
_ARITH = {ast.Add: "+", ast.Sub: "-", ast.Mult: "*", ast.Mod: "mod"}
_CMP = {ast.Eq: "=", ast.Lt: "<", ast.LtE: "<=", ast.Gt: ">", ast.GtE: ">="}


class PoTError(ValueError):
    """An invalid program; the message is written for the model that wrote it."""


def compile(program: str | dict) -> str:
    """Compile a ProofOfThought JSON program to an SMT-LIB 2.6 script."""
    if isinstance(program, str):
        try:
            program = json.loads(extract_code(program))
        except json.JSONDecodeError as e:
            raise PoTError(f"invalid JSON: {e}") from None
    if not isinstance(program, dict):
        raise PoTError("the program must be a JSON object")
    return _Compiler(program).compile()


class _Compiler:
    def __init__(self, program: dict) -> None:
        self.p = program
        self.sorts: dict[str, str] = dict(BUILTIN)  # DSL sort name -> SMT sort
        self.funcs: dict[str, tuple[list[str], str]] = {}  # name -> (domain, range), SMT sorts
        self.consts: dict[str, str] = {}  # name -> SMT sort
        self.vars: dict[str, str] = {}  # declared variables (for quantifier binders)
        self.nullary: set[str] = set()  # 0-ary functions: usable as f() (z3py) or bare f
        self.lines: list[str] = []

    def compile(self) -> str:
        p = self.p
        unknown = set(p) - {"sorts", "functions", "constants", "variables", "knowledge_base", "rules",
                            "verifications", "actions", "optimization"}  # fmt: skip
        if unknown:
            raise PoTError(f"unknown top-level keys: {sorted(unknown)}")
        if p.get("optimization"):
            raise PoTError("'optimization' is not supported by this compiler; use z3 directly")
        for sort in self._ordered_sorts(_items(p, "sorts", dict)):
            self._sort(sort)
        for f in _items(p, "functions", dict):
            self._function(f)
        constants = p.get("constants") or {}
        if isinstance(constants, list):  # [{"name": ..., "sort": ...}], like 'variables'
            constants = {c.get("name"): {"sort": c.get("sort")} for c in _items(p, "constants", dict)}
        if not isinstance(constants, dict):
            raise PoTError("'constants' must be an object mapping a category to {\"sort\": ..., \"members\": [...]}")
        for category, group in constants.items():
            self._constants(category, group)
        for v in _items(p, "variables", dict):
            name, sort = self._typed(v, "variable")
            self.vars[name] = sort
            self.consts.setdefault(name, sort)
            self.lines.append(f"(declare-const {sym(name)} {sort})")
        for item in _items(p, "knowledge_base", (str, dict)):
            self._knowledge(item)
        for rule in _items(p, "rules", dict):
            self._rule(rule)
        verifications = _items(p, "verifications", dict)
        if len(verifications) != 1:
            raise PoTError(
                f"exactly one verification is required (got {len(verifications)}); several would give ambiguous answers"
            )
        name = verifications[0].get("name", "verification")
        self.lines += [f"; verification: {name}", "(push 1)", f"(assert {self._verification(verifications[0])})",
                       "(check-sat)", "(get-model)", "(pop 1)"]  # fmt: skip
        return "\n".join(self.lines) + "\n"

    # -- declarations ------------------------------------------------------------

    def _ordered_sorts(self, defs: list[dict]) -> list[dict]:
        """ArraySorts may reference sorts declared later: order by dependency."""
        by_name, order, seen = {}, [], set()
        for d in defs:
            if not isinstance(d, dict) or "name" not in d or "type" not in d:
                raise PoTError(f"each sort needs 'name' and 'type': {d}")
            if not isinstance(d["name"], str) or not d["name"].isidentifier():
                raise PoTError(f"sort name {d['name']!r} is not a valid name")
            if not isinstance(d["type"], str):
                raise PoTError(f"the type of sort {d['name']} must be a string such as \"DeclareSort\", got {d['type']!r}")
            if d["name"] in BUILTIN:
                raise PoTError(f"{d['name']} is built in; do not declare it")
            by_name[d["name"]] = d

        def visit(name: str, path: tuple[str, ...]) -> None:
            if name in seen or name not in by_name:
                return
            if name in path:
                raise PoTError(f"circular sort definitions: {' -> '.join(path + (name,))}")
            t = by_name[name]["type"]
            if isinstance(t, str) and t.startswith("ArraySort("):
                for dep in _split_top(t[len("ArraySort(") : -1]):
                    visit(dep.strip(), path + (name,))
            seen.add(name)
            order.append(by_name[name])

        for name in by_name:
            visit(name, ())
        return order

    def _sort(self, d: dict) -> None:
        name, t = d["name"], d["type"]
        s = sym(name)
        if t == "DeclareSort":
            self.lines.append(f"(declare-sort {s} 0)")
        elif t == "EnumSort":
            values = d.get("values") or []
            if not isinstance(values, list) or not all(isinstance(v, str) and v.isidentifier() for v in values):
                raise PoTError(f"EnumSort {name} needs 'values': a list of names, got {values!r}")
            if not values:
                raise PoTError(f"EnumSort {name} needs a non-empty 'values' list")
            self.lines.append(f"(declare-datatypes (({s} 0)) (({' '.join(f'({sym(v)})' for v in values)})))")
            for v in values:
                self.consts[v] = s
        elif t in BUILTIN:  # an alias: use the underlying sort, so arithmetic type-checks
            s = BUILTIN[t]
        elif isinstance(t, str) and t.startswith("BitVecSort(") and t.endswith(")"):
            size = t[len("BitVecSort(") : -1].strip()
            if not size.isdigit() or not 0 < int(size) <= 65536:
                raise PoTError(f"invalid BitVecSort size in {name}: {size!r}")
            s = f"(_ BitVec {size})"
        elif isinstance(t, str) and t.startswith("ArraySort(") and t.endswith(")"):
            parts = [x.strip() for x in _split_top(t[len("ArraySort(") : -1])]
            if len(parts) != 2:
                raise PoTError(f"ArraySort takes two sorts: {t}")
            s = f"(Array {self._sort_ref(parts[0])} {self._sort_ref(parts[1])})"
        else:
            raise PoTError(f"unknown sort type {t!r} for {name}")
        self.sorts[name] = s

    def _sort_ref(self, name: Any) -> str:
        if not isinstance(name, str):
            raise PoTError(f"a sort must be named by a string, got {name!r}")
        if name in self.sorts:
            return self.sorts[name]
        text = name.strip() if isinstance(name, str) else ""
        if text.startswith("BitVecSort(") and text.endswith(")"):  # inline, as in z3py
            size = text[len("BitVecSort(") : -1].strip()
            if size.isdigit() and 0 < int(size) <= 65536:
                return f"(_ BitVec {size})"
        if text.startswith("ArraySort(") and text.endswith(")"):
            parts = [x.strip() for x in _split_top(text[len("ArraySort(") : -1])]
            if len(parts) == 2:
                return f"(Array {self._sort_ref(parts[0])} {self._sort_ref(parts[1])})"
        raise PoTError(f"unknown sort {name!r}; declare it under 'sorts' (built-ins: BoolSort, IntSort, RealSort, "
                       "BitVecSort(n))")  # fmt: skip

    def _function(self, f: dict) -> None:
        if not isinstance(f, dict) or not {"name", "domain", "range"} <= set(f):
            raise PoTError(f"each function needs 'name', 'domain' and 'range': {f}")
        if not isinstance(f["name"], str) or not f["name"].isidentifier():
            raise PoTError(f"function name {f['name']!r} is not a valid name")
        if not isinstance(f["domain"], list):
            raise PoTError(f"'domain' of {f['name']} must be a list of sorts, got {f['domain']!r}")
        domain = [self._sort_ref(x) for x in f["domain"]]
        rng = self._sort_ref(f["range"])
        if not domain:  # a 0-ary function is a constant
            self.consts[f["name"]] = rng
            self.nullary.add(f["name"])
        else:
            self.funcs[f["name"]] = (domain, rng)
        self.lines.append(f"(declare-fun {sym(f['name'])} ({' '.join(domain)}) {rng})")

    def _constants(self, category: str, group: Any) -> None:
        if not isinstance(group, dict) or "sort" not in group:
            raise PoTError(f"constants '{category}' needs 'sort' and 'members', e.g. "
                           f'{{"{category}": {{"sort": "Person", "members": ["alice"]}}}}')  # fmt: skip
        sort = self._sort_ref(group["sort"])
        # {"distance": {"sort": "IntSort"}} - one constant named by its key - is a common, unambiguous shorthand.
        members = group.get("members", [category])
        if isinstance(members, dict):
            members = list(members)  # ProofOfThought's legacy {"name": "alias"} form: the keys are the names
        if not isinstance(members, list):
            raise PoTError(f"'members' of constants '{category}' must be a list of names, got {members!r}")
        for name in members if isinstance(members, list) else list(members):
            if not isinstance(name, str) or not name.isidentifier():
                raise PoTError(f"constant {name!r} in '{category}' is not a valid name; constants are named "
                               "individuals (e.g. 'nancy'). Write numbers directly in expressions")  # fmt: skip
            self.consts[name] = sort
            self.lines.append(f"(declare-const {sym(name)} {sort})")

    def _typed(self, v: Any, what: str) -> tuple[str, str]:
        if not isinstance(v, dict) or "name" not in v or "sort" not in v:
            raise PoTError(f"each {what} needs 'name' and 'sort': {v}")
        if not isinstance(v["name"], str) or not v["name"].isidentifier():
            raise PoTError(f"{what} name {v['name']!r} is not a valid name")
        return v["name"], self._sort_ref(v["sort"])

    # -- statements -------------------------------------------------------------

    def _knowledge(self, item: Any) -> None:
        if isinstance(item, dict) and not isinstance(item.get("assertion"), str):
            raise PoTError(f'a knowledge_base object needs an "assertion" string (and optionally "value"), got {item}')
        text, value = (item.get("assertion"), item.get("value", True)) if isinstance(item, dict) else (item, True)
        value = _truth(value, text)
        expr = self._expr(text, {})
        self.lines.append(f"(assert {expr if value else f'(not {expr})'})")

    def _binders(self, items: list, where: str) -> dict[str, str]:
        if not isinstance(items, list):
            raise PoTError(f"the quantifier list in {where} must be a list of variables, got {items!r}")
        if not items:
            raise PoTError(f"empty quantifier list in {where}; remove the key if no quantification is needed")
        bound = {}
        for v in items:
            if isinstance(v, str):  # a variable declared under 'variables', referred to by name
                if v not in self.vars:
                    raise PoTError(f"quantified variable {v!r} in {where} is not declared under 'variables'; "
                                   'declare it there or write {"name": ..., "sort": ...}')  # fmt: skip
                bound[v] = self.vars[v]
            else:
                name, sort = self._typed(v, "quantified variable")
                bound[name] = sort
        return bound

    def _rule(self, rule: dict) -> None:
        bound = self._binders(rule["forall"], "rule") if "forall" in rule else {}
        if "implies" in rule:
            if not bound:
                raise PoTError("implication rules need a non-empty 'forall'")
            imp = rule["implies"]
            if not isinstance(imp, dict) or "antecedent" not in imp or "consequent" not in imp:
                raise PoTError("'implies' must be {\"antecedent\": ..., \"consequent\": ...}")
            body = f"(=> {self._expr(imp['antecedent'], bound)} {self._expr(imp['consequent'], bound)})"
        elif "constraint" in rule:
            body = self._expr(rule["constraint"], bound)
        else:
            raise PoTError(f"a rule needs 'implies' or 'constraint': {rule}")
        self.lines.append(f"(assert {_quantify('forall', bound, body)})")

    def _verification(self, v: dict) -> str:
        if "exists" in v:
            bound = self._binders(v["exists"], "verification")
            return _quantify("exists", bound, self._expr(v["constraint"], bound))
        if "forall" in v:
            bound = self._binders(v["forall"], "verification")
            imp = v.get("implies") or {}
            if "antecedent" not in imp or "consequent" not in imp:
                raise PoTError("a 'forall' verification needs 'implies' with 'antecedent' and 'consequent'")
            body = f"(=> {self._expr(imp['antecedent'], bound)} {self._expr(imp['consequent'], bound)})"
            return _quantify("forall", bound, body)
        if "constraint" in v:
            return self._expr(v["constraint"], {})
        raise PoTError("a verification needs 'constraint', 'exists' or 'forall'")

    # -- expressions --------------------------------------------------------------

    def _expr(self, text: Any, bound: dict[str, str]) -> str:
        if not isinstance(text, str):
            raise PoTError(f"expected an expression string, got {text!r}")
        try:
            tree = ast.parse(text.strip(), mode="eval").body
        except SyntaxError as e:
            raise PoTError(f"cannot parse expression {text!r}: {e.msg}") from None
        code, sort = self._tr(tree, bound, text)
        if sort != "Bool":
            raise PoTError(f"{text!r} has sort {sort}, but assertions must be Boolean")
        return code

    def _tr(self, n: ast.AST, env: dict[str, str], src: str) -> tuple[str, str]:
        """Translate a node to (SMT-LIB term, sort)."""
        if isinstance(n, (ast.BinOp, ast.UnaryOp)):
            # Python evaluates literal-only arithmetic before z3 ever sees it (200 + 100 is 300,
            # 7 / 2 is 3.5): fold it the same way, so literals coerce exactly as in z3py.
            value = _fold(n)
            if value is not None:
                n = ast.Constant(value)
        if isinstance(n, ast.Constant):
            if isinstance(n.value, bool):
                return ("true" if n.value else "false"), "Bool"
            if isinstance(n.value, int):
                return (str(n.value) if n.value >= 0 else f"(- {-n.value})"), "Int"
            if isinstance(n.value, float):
                if n.value != n.value or n.value in (float("inf"), float("-inf")):
                    raise PoTError(f"{n.value!r} is not a finite number in {src!r}")
                text = format(Decimal(repr(abs(n.value))), "f")
                return (text if n.value >= 0 else f"(- {text})"), "Real"
        elif isinstance(n, ast.Name):
            sort = env.get(n.id) or self.consts.get(n.id)
            if sort is None:
                if n.id in self.funcs:
                    raise PoTError(f"{n.id} is a function; apply it to arguments, e.g. {n.id}(...)")
                raise PoTError(f"unknown symbol {n.id!r} in {src!r}; declare it as a constant, variable or function")
            return sym(n.id), sort
        elif isinstance(n, ast.BoolOp):
            parts = [self._bool(x, env, src) for x in n.values]
            return f"({'and' if isinstance(n.op, ast.And) else 'or'} {' '.join(parts)})", "Bool"
        elif isinstance(n, ast.UnaryOp):
            if isinstance(n.op, ast.Not):
                return f"(not {self._bool(n.operand, env, src)})", "Bool"
            if isinstance(n.op, (ast.USub, ast.Invert)):
                code, sort = self._tr(n.operand, env, src)
                if _bv_width(sort):
                    return f"({'bvneg' if isinstance(n.op, ast.USub) else 'bvnot'} {code})", sort
                if isinstance(n.op, ast.Invert):
                    raise PoTError(f"~ needs a bit-vector in {src!r}")
                code, sort = self._num(n.operand, env, src)
                return f"(- {code})", sort
            if isinstance(n.op, ast.UAdd):
                return self._num(n.operand, env, src)
        elif isinstance(n, ast.BinOp):
            (a, sa), (b, sb) = self._tr(n.left, env, src), self._tr(n.right, env, src)
            if _bv_width(sa) or _bv_width(sb):
                (a, sa), (b, sb) = _bv_pair((a, sa), (b, sb), src)
                if type(n.op) not in _BV_ARITH:
                    raise PoTError(f"unsupported bit-vector operator in {src!r}")
                return f"({_BV_ARITH[type(n.op)]} {a} {b})", sa
            (a, sa), (b, sb) = self._num(n.left, env, src), self._num(n.right, env, src)
            sort = "Real" if "Real" in (sa, sb) else sa
            if isinstance(n.op, ast.Div):
                return (f"(div {a} {b})" if sort == "Int" else f"(/ {a} {b})"), sort
            if type(n.op) in _ARITH:
                if isinstance(n.op, ast.Mod) and sort != "Int":
                    raise PoTError(f"% needs integers in {src!r}")
                return f"({_ARITH[type(n.op)]} {a} {b})", sort
        elif isinstance(n, ast.Compare):
            terms = [self._tr(x, env, src) for x in [n.left, *n.comparators]]
            parts = []
            for op, (a, sa), (b, sb) in zip(n.ops, terms, terms[1:]):
                if _bv_width(sa) or _bv_width(sb):
                    (a, sa), (b, sb) = _bv_pair((a, sa), (b, sb), src)
                    if isinstance(op, (ast.Eq, ast.NotEq)):
                        parts.append(f"(= {a} {b})" if isinstance(op, ast.Eq) else f"(not (= {a} {b}))")
                    elif type(op) in _BV_CMP:  # z3py's < <= > >= on bit-vectors are signed
                        parts.append(f"({_BV_CMP[type(op)]} {a} {b})")
                    else:
                        break
                    continue
                if isinstance(op, (ast.Eq, ast.NotEq)):
                    if not _compatible(sa, sb):
                        raise PoTError(f"cannot compare {sa} with {sb} in {src!r}")
                    eq = f"(= {a} {b})"
                    parts.append(eq if isinstance(op, ast.Eq) else f"(not {eq})")
                elif type(op) in _CMP:
                    for s in (sa, sb):
                        if s not in ("Int", "Real"):
                            raise PoTError(f"ordering comparison on non-numeric {s} in {src!r}")
                    parts.append(f"({_CMP[type(op)]} {a} {b})")
                else:
                    break
            else:
                return (parts[0] if len(parts) == 1 else f"(and {' '.join(parts)})"), "Bool"
        elif isinstance(n, ast.Call) and isinstance(n.func, ast.Name):
            return self._call(n.func.id, n.args, env, src)
        elif isinstance(n, ast.Subscript):  # a[i], as in z3py
            index = n.slice.value if isinstance(n.slice, ast.Index) else n.slice  # type: ignore[attr-defined]
            return self._select(self._tr(n.value, env, src), self._tr(index, env, src), src)
        raise PoTError(f"unsupported syntax {ast.unparse(n)!r} in {src!r}")

    def _call(self, f: str, args: list[ast.AST], env: dict[str, str], src: str) -> tuple[str, str]:
        if f in ("ForAll", "Exists"):
            if len(args) != 2 or not isinstance(args[0], (ast.List, ast.Tuple)):
                raise PoTError(f"{f} takes a list of variables and a body: {f}([x, y], body)")
            bound = {}
            for v in args[0].elts:
                if not isinstance(v, ast.Name) or (v.id not in self.vars and v.id not in env):
                    raise PoTError(f"{f} can only bind variables declared under 'variables', not {ast.unparse(v)!r}")
                bound[v.id] = env.get(v.id) or self.vars[v.id]
            body = self._bool(args[1], {**env, **bound}, src)
            return _quantify("forall" if f == "ForAll" else "exists", bound, body), "Bool"
        if f in _NARY:
            items = args[0].elts if len(args) == 1 and isinstance(args[0], (ast.List, ast.Tuple)) else args
            if f == "Distinct":
                terms = [self._tr(x, env, src) for x in items]
                if len(terms) < 2:
                    raise PoTError(f"Distinct needs at least two terms in {src!r}")
                widths = [_bv_width(t[1]) for t in terms]
                if any(widths):  # integer literals among bit-vectors are coerced, as in z3py
                    want = next(f"(_ BitVec {w})" for w in widths if w)
                    terms = [_coerce(t, want, "Distinct argument", src) for t in terms]
                elif any(not _compatible(t[1], terms[0][1]) for t in terms):
                    raise PoTError(f"Distinct arguments must share one sort, got {sorted({t[1] for t in terms})} in {src!r}")
                return f"(distinct {' '.join(t for t, _ in terms)})", "Bool"
            return f"({_NARY[f]} {' '.join(self._bool(x, env, src) for x in items)})", "Bool"
        if f == "Not":
            self._arity(f, args, 1)
            return f"(not {self._bool(args[0], env, src)})", "Bool"
        if f == "Implies":
            self._arity(f, args, 2)
            return f"(=> {self._bool(args[0], env, src)} {self._bool(args[1], env, src)})", "Bool"
        if f == "If":
            self._arity(f, args, 3)
            (a, sa), (b, sb) = self._tr(args[1], env, src), self._tr(args[2], env, src)
            if _bv_width(sa) or _bv_width(sb):
                (a, sa), (b, sb) = _bv_pair((a, sa), (b, sb), src)
            elif not _compatible(sa, sb):
                raise PoTError(f"the branches of If have different sorts ({sa} and {sb}) in {src!r}")
            return f"(ite {self._bool(args[0], env, src)} {a} {b})", "Real" if "Real" in (sa, sb) else sa
        if f in ("Sum", "Product"):
            items = args[0].elts if len(args) == 1 and isinstance(args[0], (ast.List, ast.Tuple)) else args
            raw = [self._tr(x, env, src) for x in items]
            if any(_bv_width(t[1]) for t in raw):  # z3py's Sum/Product over bit-vectors: bvadd / bvmul
                out = raw[0]
                for nxt in raw[1:]:
                    (a, sa), (b, _) = _bv_pair(out, nxt, src)
                    out = (f"({'bvadd' if f == 'Sum' else 'bvmul'} {a} {b})", sa)
                if not _bv_width(out[1]):
                    raise PoTError(f"{f} needs bit-vectors or numbers in {src!r}")
                return out
            terms = [self._num(x, env, src) for x in items]
            if not terms:
                return "0" if f == "Sum" else "1", "Int"
            sort = "Real" if any(s == "Real" for _, s in terms) else "Int"
            if len(terms) == 1:
                return terms[0][0], sort
            return f"({'+' if f == 'Sum' else '*'} {' '.join(t for t, _ in terms)})", sort
        if f in ("Select", "Store") and f not in self.funcs:
            self._arity(f, args, 2 if f == "Select" else 3)
            array, index = self._tr(args[0], env, src), self._tr(args[1], env, src)
            if f == "Select":
                return self._select(array, index, src)
            domain, rng = self._array_parts(array[1], src)
            index = _coerce(index, domain, "Store index", src)
            value = _coerce(self._tr(args[2], env, src), rng, "Store value", src)
            return f"(store {array[0]} {index[0]} {value[0]})", array[1]
        if f in _BV_CALLS and f not in self.funcs:  # a user's own function of that name wins
            op, arity, result = _BV_CALLS[f]
            self._arity(f, args, arity)
            (a, sa), (b, sb) = _bv_pair(self._tr(args[0], env, src), self._tr(args[1], env, src), src)
            return f"({op} {a} {b})", "Bool" if result == "bool" else sa
        if f == "Concat":
            terms = [self._tr(x, env, src) for x in args]
            widths = [_bv_width(s_) for _, s_ in terms]
            if len(terms) < 2 or not all(widths):
                raise PoTError(f"Concat takes two or more bit-vectors in {src!r}")
            out = terms[0][0]
            for code, _ in terms[1:]:
                out = f"(concat {out} {code})"
            return out, f"(_ BitVec {sum(widths)})"
        if f in ("Extract", "ZeroExt", "SignExt"):
            ints = [_int_literal(x) for x in args[:-1]]
            code, sort = self._tr(args[-1], env, src) if args else ("", "")
            width = _bv_width(sort)
            if len(args) != (3 if f == "Extract" else 2) or None in ints or not width:
                raise PoTError(f"{f} takes integer literals and a bit-vector: "
                               + ("Extract(hi, lo, x)" if f == "Extract" else f"{f}(k, x)") + f" in {src!r}")  # fmt: skip
            if f == "Extract":
                hi, lo = ints
                if not 0 <= lo <= hi < width:
                    raise PoTError(f"Extract({hi}, {lo}, x) is out of range for a {width}-bit vector in {src!r}")
                return f"((_ extract {hi} {lo}) {code})", f"(_ BitVec {hi - lo + 1})"
            k = ints[0]
            ext = "zero_extend" if f == "ZeroExt" else "sign_extend"
            return f"((_ {ext} {k}) {code})", f"(_ BitVec {width + k})"
        if f == "BitVecVal":
            self._arity(f, args, 2)
            value, size = _int_literal(args[0]), _int_literal(args[1])
            if value is None or size is None or size <= 0:
                raise PoTError("BitVecVal takes two integer literals: BitVecVal(value, size)")
            return f"(_ bv{value % (1 << size)} {size})", f"(_ BitVec {size})"
        if f in self.funcs:
            domain, rng = self.funcs[f]
            self._arity(f, args, len(domain))
            terms = [_coerce(self._tr(a, env, src), want, f"argument {i} of {f}", src)
                     for i, (a, want) in enumerate(zip(args, domain), 1)]  # fmt: skip
            return f"({sym(f)} {' '.join(t for t, _ in terms)})", rng
        if f in self.nullary and not args:  # z3py: a 0-ary Function is applied as f()
            return sym(f), self.consts[f]
        if f in self.consts or f in env:
            raise PoTError(f"{f} is a constant, not a function, in {src!r}")
        raise PoTError(f"unknown function {f!r} in {src!r}; declare it under 'functions'")

    def _select(self, array: tuple[str, str], index: tuple[str, str], src: str) -> tuple[str, str]:
        domain, rng = self._array_parts(array[1], src)
        index = _coerce(index, domain, "array index", src)
        return f"(select {array[0]} {index[0]})", rng

    @staticmethod
    def _array_parts(sort: str, src: str) -> tuple[str, str]:
        """(domain, range) of an ``(Array D R)`` sort."""
        if not sort.startswith("(Array "):
            raise PoTError(f"{sort} is not an array in {src!r}")
        inner, parts, depth, start = sort[len("(Array ") : -1], [], 0, 0
        for i, c in enumerate(inner):
            depth += (c == "(") - (c == ")")
            if c == " " and depth == 0:
                parts.append(inner[start:i])
                start = i + 1
        parts.append(inner[start:])
        return parts[0], parts[1]

    def _bool(self, n: ast.AST, env: dict[str, str], src: str) -> str:
        code, sort = self._tr(n, env, src)
        if sort != "Bool":
            raise PoTError(f"expected a Boolean, but {ast.unparse(n)!r} is {sort} in {src!r}")
        return code

    def _num(self, n: ast.AST, env: dict[str, str], src: str) -> tuple[str, str]:
        code, sort = self._tr(n, env, src)
        if sort not in ("Int", "Real"):
            raise PoTError(f"arithmetic on non-numeric {sort} in {src!r}")
        return code, sort

    @staticmethod
    def _arity(f: str, args: list, n: int) -> None:
        if len(args) != n:
            raise PoTError(f"{f} expects {n} argument{'s' * (n != 1)}, got {len(args)}")


_FOLD = {ast.Add: lambda a, b: a + b, ast.Sub: lambda a, b: a - b, ast.Mult: lambda a, b: a * b,
         ast.Div: lambda a, b: a / b, ast.FloorDiv: lambda a, b: a // b, ast.Mod: lambda a, b: a % b,
         ast.Pow: lambda a, b: a**b}  # fmt: skip


def _fold(n: ast.AST) -> int | float | None:
    """The Python value of a literal-only arithmetic expression, or None."""
    if isinstance(n, ast.Constant) and isinstance(n.value, (int, float)) and not isinstance(n.value, bool):
        return n.value
    if isinstance(n, ast.UnaryOp) and isinstance(n.op, (ast.USub, ast.UAdd)):
        v = _fold(n.operand)
        return None if v is None else (-v if isinstance(n.op, ast.USub) else v)
    if isinstance(n, ast.BinOp) and type(n.op) in _FOLD:
        a, b = _fold(n.left), _fold(n.right)
        if a is None or b is None:
            return None
        if isinstance(n.op, ast.Pow) and (abs(b) > 4096 or (isinstance(a, int) and abs(a) > 2**64 and b > 1)):
            return None  # keep folding cheap and finite
        try:
            return _FOLD[type(n.op)](a, b)
        except ZeroDivisionError:
            raise PoTError(f"division by zero in {ast.unparse(n)!r}") from None
        except OverflowError:
            return None
    return None


def _split_top(text: str) -> list[str]:
    """Split on commas outside parentheses: 'IntSort, ArraySort(IntSort, BoolSort)' -> two parts."""
    parts, depth, start = [], 0, 0
    for i, c in enumerate(text):
        depth += (c == "(") - (c == ")")
        if c == "," and depth == 0:
            parts.append(text[start:i])
            start = i + 1
    parts.append(text[start:])
    return [p.strip() for p in parts]


def _items(program: dict, key: str, kind: type | tuple) -> list:
    """``program[key]`` as a list whose items are all of ``kind`` (missing means empty)."""
    value = program.get(key) or []
    if not isinstance(value, list):
        raise PoTError(f"'{key}' must be a list, got {type(value).__name__}")
    bad = [v for v in value if not isinstance(v, kind)]
    if bad:
        expected = "objects" if kind is dict else "strings or objects"
        raise PoTError(f"items of '{key}' must be {expected}; got {bad[0]!r}")
    return value


def _int_literal(n: ast.AST) -> int | None:
    """The value of an integer literal such as ``5`` or ``-1``, else None."""
    if isinstance(n, ast.UnaryOp) and isinstance(n.op, ast.USub):
        inner = _int_literal(n.operand)
        return None if inner is None else -inner
    if isinstance(n, ast.Constant) and isinstance(n.value, int) and not isinstance(n.value, bool):
        return n.value
    return None


_BV_ARITH = {ast.Add: "bvadd", ast.Sub: "bvsub", ast.Mult: "bvmul", ast.Div: "bvsdiv", ast.Mod: "bvsmod",
             ast.BitAnd: "bvand", ast.BitOr: "bvor", ast.BitXor: "bvxor", ast.LShift: "bvshl",
             ast.RShift: "bvashr"}  # fmt: skip  - exactly z3py's operator overloads
_BV_CMP = {ast.Lt: "bvslt", ast.LtE: "bvsle", ast.Gt: "bvsgt", ast.GtE: "bvsge"}
_BV_CALLS = {"ULT": ("bvult", 2, "bool"), "ULE": ("bvule", 2, "bool"), "UGT": ("bvugt", 2, "bool"),
             "UGE": ("bvuge", 2, "bool"), "UDiv": ("bvudiv", 2, "bv"), "URem": ("bvurem", 2, "bv"),
             "SRem": ("bvsrem", 2, "bv"), "LShR": ("bvlshr", 2, "bv"),
             # signed spellings (z3's C API names); z3py writes these as < <= > >=
             "SLT": ("bvslt", 2, "bool"), "SLE": ("bvsle", 2, "bool"), "SGT": ("bvsgt", 2, "bool"),
             "SGE": ("bvsge", 2, "bool")}  # fmt: skip


def _bv_width(sort: str) -> int | None:
    if sort.startswith("(_ BitVec ") and sort.endswith(")"):
        return int(sort[len("(_ BitVec ") : -1])
    return None


def _bv_pair(left: tuple[str, str], right: tuple[str, str], src: str) -> tuple[tuple[str, str], tuple[str, str]]:
    """Make two operands bit-vectors of one width, coercing integer literals as z3py does."""
    (a, sa), (b, sb) = left, right
    wa, wb = _bv_width(sa), _bv_width(sb)
    if wa and not wb:
        b, sb, wb = _bv_literal(b, sb, wa, src), sa, wa
    elif wb and not wa:
        a, sa, wa = _bv_literal(a, sa, wb, src), sb, wb
    if not (wa and wb):
        raise PoTError(f"expected bit-vectors in {src!r}")
    if wa != wb:
        raise PoTError(f"bit-vector widths differ ({wa} vs {wb}) in {src!r}; use ZeroExt/SignExt/Extract")
    return (a, sa), (b, sb)


def _bv_literal(code: str, sort: str, width: int, src: str) -> str:
    """An integer literal as a bit-vector of ``width`` (two's complement, like z3py)."""
    if sort == "Int":
        text = code[3:-1].strip() if code.startswith("(- ") else code
        if text.isdigit():
            value = -int(text) if code.startswith("(- ") else int(text)
            return f"(_ bv{value % (1 << width)} {width})"
    raise PoTError(f"cannot mix a bit-vector with a {sort} in {src!r}; use BitVecVal(value, {width})")


def _coerce(term: tuple[str, str], want: str, what: str, src: str) -> tuple[str, str]:
    """``term`` as sort ``want``: integer literals become bit-vectors (as in z3py); otherwise sorts must agree."""
    code, sort = term
    if _bv_width(want) and sort == "Int":
        return _bv_literal(code, sort, _bv_width(want), src), want
    if not _compatible(sort, want):
        raise PoTError(f"{what} must be {want}, got {sort} in {src!r}")
    return term


def _compatible(a: str, b: str) -> bool:
    return a == b or {a, b} == {"Int", "Real"}


def _quantify(q: str, bound: dict[str, str], body: str) -> str:
    if not bound:
        return body
    return f"({q} ({' '.join(f'({sym(v)} {s})' for v, s in bound.items())}) {body})"


_SIMPLE = set("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789~!@$%^&*_-+=<>.?/")


def sym(name: str) -> str:
    """An SMT-LIB symbol for a DSL name: quoted when it is reserved, starts with a digit, or is not
    plain ASCII (SMT-LIB simple symbols are ASCII-only, so ``jürgen`` becomes ``|jürgen|``)."""
    if not isinstance(name, str) or not name or "|" in name or "\\" in name:
        raise PoTError(f"invalid name {name!r}")
    if name in _RESERVED or name[0].isdigit() or not set(name) <= _SIMPLE:
        return f"|{name}|"
    return name


def _truth(value: Any, text: Any) -> bool:
    """A knowledge-base ``value``: true/false, also when written as a string ("false" is false)."""
    if isinstance(value, bool):
        return value
    if isinstance(value, str) and value.strip().lower() in ("true", "false", "yes", "no", "1", "0"):
        return value.strip().lower() in ("true", "yes", "1")
    if isinstance(value, int):
        return bool(value)
    raise PoTError(f"'value' of {text!r} must be true or false, got {value!r}")


GUIDANCE = """Write one JSON object (optionally in a ```json block) with these keys:
- "sorts": [{"name": "Person", "type": "DeclareSort"}] - also "EnumSort" (+ "values": [...]), "BitVecSort(8)", "ArraySort(A, B)". Built in: BoolSort, IntSort, RealSort (never declare these).
- "functions": [{"name": "is_democrat", "domain": ["Person"], "range": "BoolSort"}]
- "constants": {"people": {"sort": "Person", "members": ["nancy"]}}
- "variables": [{"name": "p", "sort": "Person"}] - variables that ForAll/Exists may bind
- "knowledge_base": ["is_democrat(nancy)", {"assertion": "f(a)", "value": false}]
- "rules": [{"forall": [{"name": "p", "sort": "Person"}], "implies": {"antecedent": "...", "consequent": "..."}}] or {"constraint": "..."}
- "verifications": exactly one: {"name": "q", "constraint": "..."} (or "exists": [...] + "constraint", or "forall": [...] + "implies")
Expressions use z3py syntax: And, Or, Not, Implies, If, Distinct, Sum, Product, ForAll([x], ...), Exists([x], ...), == != < <= > >= + - * / %.
Write numbers directly in expressions (n == 366); constants are named individuals. Bit-vectors: BitVecVal(v, n), + - * / % & | ^ ~ << >> and < <= > >= (signed, as in z3py), ULT/ULE/UGT/UGE/UDiv/URem/LShR, Concat, Extract(hi, lo, x), ZeroExt/SignExt(k, x). Arrays: a[i], Select(a, i), Store(a, i, v).
The verification is checked against the knowledge base and rules: sat = consistent with them, unsat = contradicts them. To PROVE that the premises entail a claim, verify Not(claim): unsat proves the claim."""

EXAMPLE = json.dumps(
    {
        "sorts": [{"name": "Person", "type": "DeclareSort"}],
        "functions": [
            {"name": "is_democrat", "domain": ["Person"], "range": "BoolSort"},
            {"name": "supports_abortion", "domain": ["Person"], "range": "BoolSort"},
        ],
        "constants": {"people": {"sort": "Person", "members": ["nancy"]}},
        "knowledge_base": ["is_democrat(nancy)"],
        "rules": [{"forall": [{"name": "p", "sort": "Person"}],
                   "implies": {"antecedent": "is_democrat(p)", "consequent": "supports_abortion(p)"}}],
        "verifications": [{"name": "entailed", "constraint": "Not(supports_abortion(nancy))"}],
    },
    indent=1,
)  # fmt: skip


def backend():
    """The ``pot`` backend: this DSL, compiled to SMT-LIB and run on z3."""
    from formalkit.client import backend as get, compiled

    return compiled(
        get("z3"),
        compile,
        name="pot",
        language="Proof of Thought JSON DSL",
        emits="a JSON program of sorts, functions, constants, a knowledge base, rules and one verification.",
        guidance=GUIDANCE,
        example=EXAMPLE,
    )
