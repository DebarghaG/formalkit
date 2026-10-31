from __future__ import annotations

import json

from formalkit.core import Result, Spec, Verdict
from formalkit.server import Adapter, sh, timed_out, workdir

MAX_SOLUTIONS = 10

# Loads the program, collecting every `?- Goal.` line as a query (with its
# variable names) instead of running it as a directive, then answers each
# query with up to MAX_SOLUTIONS solutions as one JSON line - written to a
# results file, so whatever the program prints cannot corrupt the protocol.
# A final {"done": true} line tells the adapter every query ran (a program
# calling halt/0 stops early).
DRIVER = r"""
:- use_module(library(http/json)).
:- use_module(library(time)).
:- dynamic fk_query/2.
user:term_expansion((?- G), fk_query(G, B)) :- prolog_load_context(variable_names, B).

fk_main(File, Results, Limit, TimeLimit) :-
    open(Results, write, Out, [encoding(utf8)]),
    nb_setval(fk_out, Out),
    style_check(-singleton), style_check(-discontiguous),
    op(900, fy, user:not),  % `not p(X)` reads as SWI's not/1 (negation as failure), as models often write it
    consult(File),
    absolute_file_name(File, Abs),
    fk_close_world(Abs),
    findall(G-B, fk_query(G, B), Qs),
    get_time(Now), Deadline is Now + TimeLimit,  % all queries share one time budget
    forall(member(G-B, Qs), fk_run(G, B, Limit, Deadline)),
    fk_emit(_{done: true}),
    close(Out).

% Closed world: a predicate that the program's rules call but that has no
% clauses is false (declared dynamic) instead of an existence error. Library
% and built-in predicates are left alone; queries naming a predicate the
% program never mentions still raise (likely a typo).
fk_close_world(File) :-
    findall(N/A, fk_missing(File, N, A), Ms0), sort(Ms0, Ms),
    forall(member(N/A, Ms), dynamic(user:N/A)),
    findall(S, (member(N/A, Ms), format(string(S), "~w/~w", [N, A])), Names),
    ( Names == [] -> true ; fk_emit(_{closed_world: Names}) ).

fk_missing(File, N, A) :-
    current_predicate(user:PN/PA), functor(H, PN, PA),
    \+ predicate_property(user:H, imported_from(_)),
    catch(clause(user:H, Body, Ref), _, fail),
    clause_property(Ref, file(File)),  % only the program's own clauses
    fk_goal(Body, G), callable(G), functor(G, N, A),
    \+ current_predicate(user:N/A), \+ predicate_property(system:G, defined),
    \+ '$in_library'(N, A, _).

fk_goal(V, _) :- var(V), !, fail.
fk_goal((A, B), G) :- !, ( fk_goal(A, G) ; fk_goal(B, G) ).
fk_goal((A ; B), G) :- !, ( fk_goal(A, G) ; fk_goal(B, G) ).
fk_goal((A -> B), G) :- !, ( fk_goal(A, G) ; fk_goal(B, G) ).
fk_goal((A *-> B), G) :- !, ( fk_goal(A, G) ; fk_goal(B, G) ).
fk_goal(\+ A, G) :- !, fk_goal(A, G).
fk_goal(not(A), G) :- !, fk_goal(A, G).
fk_goal(call(A), G) :- !, fk_goal(A, G).
fk_goal(findall(_, A, _), G) :- !, fk_goal(A, G).
fk_goal(forall(A, B), G) :- !, ( fk_goal(A, G) ; fk_goal(B, G) ).
fk_goal(M:A, G) :- !, M == user, fk_goal(A, G).  % other modules' goals (e.g. clpfd expansions) are theirs
fk_goal(G, G).

fk_emit(D) :-
    nb_getval(fk_out, Out),
    json_write_dict(Out, D, [width(0)]), nl(Out), flush_output(Out).

fk_show(T, B, S) :-
    format(string(S), "~W", [T, [variable_names(B), quoted(true), portray(true), max_depth(50)]]).

fk_run(G, B, Limit, Deadline) :-
    fk_show(G, B, GS),
    Limit1 is Limit + 1,
    get_time(Now), Left is max(0.1, Deadline - Now),
    catch(call_with_time_limit(Left, findnsols(Limit1, B, G, Sols0)), E, true),
    !,
    (   E == time_limit_exceeded
    ->  D = _{query: GS, status: timeout}
    ;   nonvar(E)
    ->  fk_msg(E, Msg), D = _{query: GS, status: error, error: Msg}
    ;   length(Sols0, N),
        (   N > Limit
        ->  More = true, length(Sols, Limit), append(Sols, _, Sols0)
        ;   More = false, Sols = Sols0
        ),
        maplist(fk_binding(B), Sols, Bs),
        (Sols == [] -> St = false ; St = true),
        D = _{query: GS, status: St, solutions: Bs, more: More}
    ),
    fk_emit(D).

fk_binding(B, Sol, Dict) :-
    findall(K-V, ( member(N=Val, Sol), \+ sub_atom(N, 0, _, _, '_'), nonvar(Val),  % unbound: nothing to report
                   atom_string(N, KS), atom_string(K, KS), fk_show(Val, B, V) ), Pairs),
    dict_pairs(Dict, _, Pairs).

fk_msg(E, S) :-
    catch(( '$messages':translate_message(E, Lines, []),
            with_output_to(string(S0), print_message_lines(current_output, '', Lines)) ),
          _, S0 = ""),
    (   ( S0 == "" ; sub_string(S0, 0, _, _, "Unknown message") )
    ->  format(string(S), "uncaught exception: ~q", [E])
    ;   S = S0
    ).
"""


class Prolog(Adapter):
    spec = Spec(
        name="prolog",
        premise_check="?- true.",
        family="LP",
        language="Prolog (SWI-Prolog)",
        emits="facts and rules, plus queries written as `?- Goal.` lines.",
        authority="SLD resolution with negation as failure under the closed-world assumption.",
        feedback="for each query: up to 10 variable bindings, failure, or the exception raised; load errors.",
        use="rule systems, relational and recursive reasoning, deductive databases.",
        guidance=(
            "Write the program, then one or more queries as lines `?- Goal.` (they are collected and run after the "
            "whole program loads, in order). Each query returns up to 10 solutions (bindings of its named "
            "variables) in details.queries. Verdict: sat if every query has at least one solution, unsat if some "
            "query fails (false under the closed-world assumption), error on load/syntax errors or an exception "
            "(e.g. unknown procedure), unknown on timeout. To PROVE a claim, query it; to show it does not hold, "
            "query `\\+ Claim` (or `not Claim`). A predicate your rules call but never define is simply false "
            "(closed world; listed in details.closed_world); querying a predicate the program never mentions is "
            "an error (likely a typo). Do not call halt/0; anything the program prints is shown "
            "separately from the query results. For recursive relations over cyclic data, use tabling "
            "(`:- table path/2.`) so queries terminate."
        ),
        example="parent(tom, bob).\nparent(bob, ann).\ngrandparent(X, Z) :- parent(X, Y), parent(Y, Z).\n?- grandparent(tom, Who).",
    )

    def run(self, code: str, timeout: float, **inputs: str) -> Result:
        with workdir({"program.pl": code, "driver.pl": DRIVER}) as d:
            goal = f"fk_main('program.pl', 'fk_results.jsonl', {MAX_SOLUTIONS}, {max(1, int(timeout))})"
            proc = sh(["swipl", "-q", "-g", goal, "-t", "halt", "driver.pl"], cwd=d, timeout=timeout + 5)
            prefix = f"{d}/"
            results = d / "fk_results.jsonl"
            lines = results.read_text(errors="replace").splitlines() if results.exists() else []
        queries, done, closed = [], False, []
        for line in lines:
            try:
                row = json.loads(line)
            except ValueError:
                continue
            if row.get("done"):
                done = True
            elif "closed_world" in row:
                closed = row["closed_world"]
            elif "query" in row:
                if "error" in row:
                    row["error"] = row["error"].strip().replace("call_cleanup/2: ", "")
                queries.append(row)
        stderr = proc.stderr.replace(prefix, "")  # paths relative to the program, not our temp dir
        if proc.timed_out:  # report the queries that did finish
            finished = "\n".join(_render(q) for q in queries)
            note = "time limit reached before all queries ran (a goal or directive that never terminates?)"
            result = timed_out(proc, f"{finished}\n{note}".strip())
            result.details["queries"] = queries
            return result
        load_errors = [ln for ln in stderr.splitlines() if ln.startswith("ERROR")]
        details = {"queries": queries}
        report = [_render(q) for q in queries]
        if closed:  # predicates the rules call but that have no clauses: false under the closed world
            details["closed_world"] = closed
            report.append(f"(no clauses, so false under the closed-world assumption: {', '.join(closed)})")
        printed = _clip(proc.stdout.strip())
        if printed:
            report.append(f"(the program printed)\n{printed}")
        if load_errors:
            return Result(Verdict.ERROR, "\n".join(load_errors + report), details)
        if not done:
            note = "the program stopped before all queries ran (do not call halt/0 or exit the process)"
            return Result(Verdict.ERROR, "\n".join(report + [note]), details)
        if not queries:
            return Result(Verdict.ERROR, "\n".join(report + ["no queries found; add lines like `?- Goal.`"]), details)
        statuses = {q["status"] for q in queries}
        warnings = [ln for ln in stderr.splitlines() if ln.strip()]
        text = "\n".join(report + warnings)
        if "error" in statuses:
            return Result(Verdict.ERROR, text, details)
        if "timeout" in statuses:
            return Result(Verdict.UNKNOWN, text, {**details, "timeout": True})
        if False in statuses:
            return Result(Verdict.UNSAT, text, details)
        details["model"] = {q["query"]: q["solutions"] for q in queries}  # bindings per query
        return Result(Verdict.SAT, text, details)


def _clip(text: str, limit: int = 2000) -> str:
    return text if len(text) <= limit else text[:limit] + f"\n... ({len(text) - limit} more characters)"


def _render(q: dict) -> str:
    head = f"?- {q['query']}."
    if q["status"] == "error":
        hint = ""
        if "Stack limit" in q.get("error", ""):
            hint = "\n   hint: cyclic or left-recursive rules: add `:- table name/arity.` for the recursive predicates"
        return f"{head}\n   error: {q.get('error', '')}{hint}"
    if q["status"] == "timeout":
        return f"{head}\n   timeout"
    if q["status"] is False:
        return f"{head}\n   false."
    sols = [", ".join(f"{k} = {v}" for k, v in s.items()) or "true" for s in q["solutions"]]
    more = "\n   ... (more solutions)" if q.get("more") else ""
    return head + "".join(f"\n   {s} ;" for s in sols).rstrip(" ;") + "." + more


ADAPTER = Prolog()
