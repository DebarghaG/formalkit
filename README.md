# formalkit

**One interface between LLMs and formal tools.**

SMT-LIB gave every SMT solver one input language and one answer vocabulary,
so any tool can talk to Z3, cvc5 or Yices the same way. formalkit does the
same one level up, for every kind of formal backend an LLM might use: SMT
and SAT solvers, interactive theorem provers, first-order provers, logic and
answer-set programming, planners, model checkers, CP/MILP solvers and
program verifiers.

Each tool runs in its own Docker container behind one tiny protocol:

```
run(code) -> Result(verdict, output, details)
verdict ∈ { proved, refuted, sat, unsat, optimal, unknown, error }
```

On top of that protocol sit the ways LLMs and formal tools are combined:
the agent loop from [ProofOfThought](https://github.com/DebarghaG/proofofthought),
where the LLM uses the tools as an iterative scratchpad and may only `finish`
once decisive verdicts back its answer, plus reference implementations of the
other integration patterns: translate-and-solve, self-refinement,
autoformalization, sketch-and-fill, step-level proof search, CEGIS,
auxiliary constructions and voting over formalizations.

```python
import formalkit

z3 = formalkit.backend("z3")                 # starts the container on first use
r = z3.run("(declare-const x Int) (assert (> x 5)) (assert (< x 3)) (check-sat)")
r.verdict        # Verdict.UNSAT
r.feedback()     # 'verdict: unsat\nunsat'  <- what an LLM sees

llm = formalkit.LLM(openai_client, "gpt-5")
agent = formalkit.Agent(llm, backends=["z3", "clingo", "lean"])
answer = agent.solve("Is there an integer greater than 5 and less than 3?")
print(answer)    # No  [z3: unsat]
answer.verified, answer.evidence, answer.recheck()
```

## Install

```bash
pip install -e .              # the library has no dependencies
pip install -e '.[agent]'     # + openai, for Agent / `formalkit solve`
formalkit build z3 clingo     # build images (or let first use build them)
```

Requires Docker. Images build natively on both amd64 and arm64.

## The pieces

formalkit is a few small layers, each usable on its own:

| layer | pieces | what it is |
|---|---|---|
| protocol | `Verdict`, `Result`, `Spec` | One answer vocabulary: `proved` / `refuted` / `sat` / `unsat` / `optimal` are *decisive*; `unknown` (gave up) and `error` (input rejected) are not. A `Result` holds the verdict, the raw `output` (what a model reads; `feedback()` truncates it), and `details`. The standard detail keys `model`, `counterexample`, `goals`, `proof` and `core` (the named parts to blame) mean the same thing for every backend. |
| backends | `Backend`, `State` | Anything with `.spec` and `.run(code, **inputs)`. Every backend can produce an LLM tool definition with `.tool("openai" \| "anthropic" \| "mcp")` and execute one with `.call(args)`. Backends with sessions (Lean) also have `.start(code) -> State` and `state.apply(step) -> State`, for step-by-step proving. |
| composition | `compiled`, `portfolio` | Wrappers that are backends themselves: an intermediate representation compiled to another backend, or several backends raced on one input. |
| models | `LLM` | One thin wrapper over any OpenAI-compatible client: `chat`, `ask(prompt, n=...)`, usage accounting. |
| agent | `Agent`, `Answer`, `Step` | The ProofOfThought tool loop over any backends, with four hooks (`evidence`, `render`, `nudge`, `on_step`). |
| observers & reuse | `observe`, `Trace`, `Budget`, `Library`, `premises` | Every run, step and LLM call as an event: training data, cost control, logging. A library of verified lemmas. Theories formalized once and queried many times. |
| patterns | `formalkit.patterns` | Reference implementations of the integration designs in the literature, by survey axis (see below). |
| learning | `formalkit.learn` | Rewards, rollouts, curricula, expert iteration, repair pairs, prefix labels, evaluation by execution. |

Every backend's `Spec` records the contract between model and tool: what the
model **emits**, what the tool has **authority** to decide, what **feedback**
it returns, and its typical **use**. `formalkit spec <name>` prints it.

## Backends

| family | backend | model writes | verdicts |
|---|---|---|---|
| SMT | `z3` | SMT-LIB 2.6 | sat · unsat · unknown · error |
| SMT | `cvc5` | SMT-LIB 2.6 | sat · unsat · unknown · error |
| SAT | `kissat` | DIMACS CNF | sat (assignment) · unsat (DRAT proof checked by drat-trim) |
| ITP | `lean` | Lean 4 + Mathlib | proved · unknown (`sorry`) · error (messages, unsolved goals) |
| ITP | `isabelle` | Isabelle/HOL theories (Sledgehammer available) | proved · refuted (Nitpick/Quickcheck) · unknown (`sorry`) · error (subgoals) |
| ITP | `metamath` | Metamath (`$[ set.mm $]` includes the bundled library) | proved · unknown (`?` steps) · error (failing step) |
| FOL | `vampire` | TPTP | proved · refuted · sat · unsat (via SZS status) |
| FOL | `prover9` | LADR | proved · unknown (search exhausted is not a disproof) |
| FOL | `mace4` | LADR | refuted (countermodel) · sat (model) · unknown |
| KB | `idp` | FO(·) / IDP-Z3 | sat · unsat · optimal |
| LP | `prolog` | SWI-Prolog with `?- Goal.` queries | sat (bindings) · unsat (a query failed) · error |
| LP | `problog` | ProbLog | sat (probabilities) · unsat (inconsistent evidence) |
| ASP | `clingo` | ASP-Core-2 | sat (answer sets) · unsat · optimal |
| Planning | `downward` | PDDL domain + `problem` (optional `mode`, `plan`) | sat/optimal (VAL-validated plan) · unsat · refuted (supplied plan fails VAL) |
| LTL | `spin` | Promela + `ltl` blocks | proved · refuted (counterexample trail) |
| CP | `minizinc` | MiniZinc (+ optional `data`, `solver`) | sat · optimal · unsat |
| CP | `cpmpy` | Python defining `model` (CPMpy → OR-Tools CP-SAT) | sat · optimal · unsat |
| MP | `pyomo` | Python defining `model` (Pyomo → HiGHS / Gurobi) | optimal · sat · unsat |
| Verifier | `cbmc` | C with `assert` | proved (bounded, unwinding-checked) · refuted (trace) · unknown |
| Verifier | `esbmc` | C/C++ | proved (bounded or k-induction) · refuted (trace) · unknown |
| Verifier | `framac` | ACSL-annotated C | proved · unknown (unproved goals listed) |
| Verifier | `ultimate` | C (SV-COMP) | proved (unbounded) · refuted (path / non-termination) |
| Domain | `ddar` | AlphaGeometry problems | proved (DD+AR proof) · refuted (numeric counterexample) · unknown |

Every backend can also return `error` (input rejected; the feedback says why) and
`unknown` (timeout or the tool gave up). Each backend's `guidance` (see `formalkit spec <name>`)
describes its input conventions.

`formalkit list` shows which ones are built and running.

## Using it with LLMs

**The built-in agent** works with any OpenAI-compatible client: OpenAI, Azure,
DeepSeek, vLLM, sglang, Ollama, LiteLLM.

```python
from openai import OpenAI
llm = formalkit.LLM(OpenAI(base_url="https://api.deepseek.com"), "deepseek-flash")
agent = formalkit.Agent(llm, backends=["z3", "clingo"])
answer = agent.solve(question, answer_format="Answer Yes or No.")
answer.answer, answer.verified, answer.verdict, answer.evidence, answer.steps, answer.usage
```

The loop follows ProofOfThought's agentic scratchpad. Every run is numbered
(`run #3`), and `finish(answer, evidence=[2, 3])` cites the runs that establish
the answer. An answer such as "the minimum is 3" needs two of them: 3 is
feasible (`sat`) and 2 is not (`unsat`). Tool runs within a turn execute before
`finish`. A turn without a tool call gets a nudge chosen from the last verdict.
Textual tool calls that local servers fail to parse (hermes JSON, qwen XML)
are recovered. A proof on the final turn earns one extra turn to finish.

**Hooks.** These are plain callables, so you never need to subclass:

```python
formalkit.Agent(
    llm, backends=["z3"],
    evidence=formalkit.nonvacuous(),       # which runs back an answer; raise Rejected(reason) to push back
    render=lambda result: ...,             # how a Result is shown to the model
    nudge=lambda steps: ...,               # what to say after a turn without a tool call
    on_step=trajectory.append,             # observe every run
)
```

`evidence` decides what counts as proof. The default, `cited_or_last`, takes
the cited runs (or else the last run) and requires each to be decisive.
`nonvacuous()` adds a check that the paper's "authority" question makes
necessary. A proof by contradiction proves nothing if the premises are
already contradictory, so for each `unsat` it re-runs the script without its
last assertion (the negated claim). It rejects the answer when that run is
`unsat` too. Otherwise it adds that run to the evidence, so `recheck()`
covers it as well.

**Your own loop.** Backends are plain tools:

```python
tools = [b.tool("anthropic") for b in formalkit.backends("lean", "z3")]
...
result = backend.call(tool_use.input)          # -> Result
tool_result_text = result.feedback()
```

See `examples/custom_loop.py`.

**MCP.** Expose backends to Claude Code, Claude Desktop or any MCP client:

```bash
claude mcp add formalkit -- formalkit mcp z3 lean clingo
```

**CLI.**

```bash
formalkit run z3 problem.smt2                      # prints verdict + output; exit 0 iff decisive
formalkit run downward domain.pddl -i problem=problem.pddl --json
formalkit solve "Who owns the dog? ..." -b z3,clingo -m deepseek-flash --base-url https://api.deepseek.com
formalkit up lean && formalkit down lean      # `down --all` stops every backend
```

## Patterns

`formalkit.patterns` implements the integration designs from the literature
as short functions over the same pieces, organized along the three axes of
the survey: what the model emits, what the backend does, and how systems
learn from what it returns. Each is a few dozen readable lines, meant to be
used as is or adapted.

### What the model emits (§3)

| pattern | the model emits / the tool's role | in the literature |
|---|---|---|
| `refine(llm, backend, problem, rounds=3)` | a complete program; solver errors drive regeneration (`rounds=1`, or `translate_and_solve`, is one shot) | LINC, SATLM, Logic-LM, OptiMUS |
| `Agent` | programs as tool calls; verdicts drive repair; `finish` needs evidence | Proof of Thought (agentic) |
| `formalize(llm, lean, statement)` | a formal statement with a `sorry` proof, repaired until it elaborates | autoformalization as the first stage of proving |
| `sketch_and_fill(backend, sketch, close=llm_close(llm))` | a proof sketch with holes; automation and the model close each subgoal | Draft, Sketch, and Prove |
| `step_search(lean.start(thm), llm_steps(llm))` | one tactic at a time; best-first search over checked proof states | GPT-f |
| `cegis(propose, verify)` | candidates; the verifier answers with counterexamples | CEGIS planning, invariant synthesis |
| `propose_until_proved(ddar, problem, propose)` | only what the engine cannot invent (auxiliary constructions) | AlphaGeometry |
| `vote(sample(llm, backend, problem, n=5))` | several formalizations, ranked by agreement | multiple candidate formalizations |
| `formalkit.backend("pot")` | an intermediate representation (Proof of Thought's JSON DSL), compiled to SMT-LIB | Proof of Thought, LLM-Sym |

### What the backend does (§4)

| pattern | role of the backend | in the literature |
|---|---|---|
| `repair(backend, code, fixers=[tactic_swap(AUTOMATION["lean"])], llm=llm)` | localizes the error; symbolic fixes are tried before the model | Baldur, PALM, Lyra, CoqPilot |
| `decompose(llm, lean, sketch, depth=2)` | checks sketches with `have … := by sorry` subgoals, recursively | POETRY, DeepSeek-Prover-V2, Delta Prover |
| `step_search(..., value=critic)`, `mix(*proposers)`, `Budget` | search environment; critics, diverse proposers and cost control are hooks | HTPS, LeanProgress, MPS-Prover, EconProver |
| `llm_steps(llm, context=lib.context())`, `Library` | state-dependent retrieval; a library of verified lemmas that grows | REAL-Prover, Rango, LEGO-Prover |
| `houdini(candidates, check)` | prunes a pooled candidate set using the named failures in `result.core` | Kamath et al., LaM4Inv, iRank |
| `assume_and_discharge(propose, prove_under, discharge)` | sole proof authority for a proposed assumption and for the goal under it | Lemur |
| `premises(idp_or_z3, theory)` | one formalization, checked for consistency, many queries | VERUS-LM |
| `route(llm, problem, backends)` | chooses the formalism and solver for each problem | adaptive formalism selection |
| `instantiate(llm, z3, script)` | the solver stays in control; model-proposed quantifier instances are validated first | AquaForte |
| `soft_facts(llm, problog, program)` | the model scores atoms; ProbLog does the logic exactly | OrLog |
| `lns(llm_neighborhood(llm, model), minizinc, model)` | the model picks the neighborhood; the solver searches it | LLM-LNS |

### Learning from formal feedback (§5) — `formalkit.learn`

formalkit is not a trainer: it is the environment and the labeller.

| function | produces | in the literature |
|---|---|---|
| `Trace()` observer: `.proofs()`, `.tactics()`, `.preferences()` | verified proofs; (goals, tactic, outcome) triples including failures; DPO pairs | expert iteration, LLMSTEP, failed search paths, BFS-Prover |
| `rollouts(llm, backend, problems, k=8, pinned=True)` | groups of completions with rewards from the checker | RLPAF, GRPO over checked rollouts |
| `expert_iteration(problems, attempt, train=...)` + `Curriculum` | verified solutions per round, focusing on problems of the right difficulty | Polu et al., DeepSeek-Prover, Goedel-Prover, STP |
| `repair_pairs(steps)`, `prefix_labels(code, result)` | (broken, diagnostics, fixed) triples; per-line labels up to the first error | APRIL, FormL4's process-supervised verifier |
| `conjecture(llm, lean, seed)` | new statements, filtered for validity and non-triviality | LeanConjecturer, STP |
| `backtranslate`, `cycle_consistency` | informal versions of formal statements; a semantic-preservation score | ProofNet, MMA, NL2Lean |
| `smt_equivalent`, `lean_equivalent`, `unique`, `differential`, `label`, `best_of` | formal equivalence, solution uniqueness, solver disagreement, labels for partial programs | VERGE, PuzzleClone, LAST, Schrader et al. |
| `evaluate(problems, solve, judge)` | syntactic validity, decisiveness and semantic accuracy by execution | LLASP |

**Pinned statements.** With `refine(..., template=stmt)`,
`rollouts(..., pinned=True)`, `pin(stmt)`, or the backend `pinned(lean, stmt)`
(usable by an `Agent` or over MCP), the model writes only the text that fills
the statement's `sorry`. It can never prove an easier statement
than the one asked. Without pinning, a model asked to prove `2 + 2 = 5`
proved `¬(2 + 2 = 5)` instead, and a checker that sees only the file rightly
said "proved". Pinning does not assume an indentation style: when the
model's text could be read either relative to the hole or at file level,
both layouts are produced and the checker decides.

```python
from formalkit.patterns import formalize, sketch_and_fill, step_search, llm_close, llm_steps

lean = formalkit.backend("lean")
stmt = formalize(llm, lean, "The sum of the first n odd numbers is n squared.")
filled = sketch_and_fill(lean, stmt.arguments["code"], close=llm_close(llm))  # automation, then the model
if not filled.proved:
    search = step_search(lean.start(stmt.arguments["code"]), llm_steps(llm), budget=30)
    print(search.proof)                                            # a kernel-checked proof file
```

## Evaluating pipelines, abstaining, and guarding agents

Every stage of a neuro-symbolic pipeline can fail on its own. A statement can
type-check without meaning the right thing, and a program can run while
solving the wrong problem. So formalkit measures each stage separately:

```python
from formalkit.learn import evaluate

report = evaluate(problems, solve=lambda p: agent.solve(p["question"]),
                  judge=lambda p, ans: ans.answer == p["answer"],        # tool-computed ground truth
                  fidelity=lambda p, ans: ...,                           # does the formalization mean the problem?
                  k=3)                                                   # independent runs per problem
print(report.summary())
# executable / decisive / verified / faithful / correct / false_accept / pass@k / pass^k / mean_repairs / mean_tokens
```

`false_accept` counts answers that are *verified yet wrong*, the failure
formal methods exist to prevent. `pass^k` counts problems solved in *every*
one of k runs, which is reliability rather than luck.

**Selective verification.** `consensus(lambda: agent.solve(q), n=5,
threshold=0.6)` answers only when independent runs agree on a verified answer
often enough, and otherwise abstains. Failed and unverified runs count against
the answer.

**A formal policy in an agent's runtime path.** A `Guard` checks each proposed
action against an SMT policy *before* it runs:

```python
guard = formalkit.Guard(formalkit.backend("z3"), POLICY, encode)  # POLICY: SMT-LIB with named rules
guard.check("transfer", {"to": "acct-9931", "amount": 50})   # Decision(allowed=False, reason="violates: no_sanctioned_payee")
formalkit.Agent(llm, backends=[...], guard=guard)             # blocked calls never execute; see answer.blocked
```

`encode(name, args)` turns a tool call into facts about the action. The call
is allowed if and only if the policy plus those facts is satisfiable, and the
unsat core names the rules it would break. The guard fails closed: an unknown
verdict, a solver error, or a crashing encoder all block the call. Any agent
framework can use it: `guard(name, args)` returns `None` to allow, or the
reason to block.

**User-scenario evaluations.** `evals/run.py` runs the pipelines four kinds of
real users run, against a real model and the real tools:

| scenario | the user | pipeline | what it reports |
|---|---|---|---|
| `researcher` | evaluates an LLM+solver pipeline | `Agent` over z3 and clingo on fresh "who owns what" puzzles | per-stage rates, pass^k; consensus precision vs abstention |
| `data_builder` | builds verified training data | `formalize` then a pinned proof in Lean, on true and false statements | fidelity (Lean-checked equivalence with the reference), proofs of false statements, usable data |
| `practitioner` | solves optimization problems | `Agent` over MiniZinc, CPMpy and Pyomo on knapsack problems | per-stage rates, "ran but answered wrong" |
| `agent_builder` | deploys an agent with real side effects | a banking agent with or without rules in its prompt, with or without a `Guard` | policy violations executed, blocks, false blocks |

Problems are generated with random names and numbers, so a memorized puzzle
won't help. Ground truth is computed by code (brute force, or true by
construction), never written by hand. Every result is reported per stage
over `k` runs.

```bash
OPENAI_BASE_URL=https://api.deepseek.com OPENAI_API_KEY=... python evals/run.py --n 8 --k 3 --model deepseek-flash
```

## Observers, budgets and libraries

```python
trace, budget = formalkit.Trace(), formalkit.Budget(calls=500, tokens=2_000_000, seconds=3600)
with formalkit.observe(trace), formalkit.observe(budget):
    answer = agent.solve(question)        # ends cleanly with answer.error when the budget runs out
write_jsonl("tactics.jsonl", trace.tactics())
```

Every backend run, session step and LLM call is an `Event`, and observers
see all of them, including those inside patterns, portfolios and worker
threads. Observers apply process-wide while their `with` block is active.
`Library` holds verified artifacts: an entry is *proved* only when a
backend's result says so. `lib.search(goal)` retrieves entries,
`lib.context()` feeds them to the LLM patterns, and `lib.attach(lean)` makes
every proved lemma available to later proofs by name.

## Composing backends

Wrappers are backends themselves, so the agent, the patterns, MCP and the CLI
use them unchanged:

```python
pot = formalkit.backend("pot")                         # PoT JSON DSL -> SMT-LIB -> z3 (a registered IR)
mine = formalkit.compiled(z3, my_compiler, name="mydsl", language="MyDSL", emits="...")
fol = formalkit.portfolio(prover9, mace4)              # race a proof against a countermodel
smt = formalkit.portfolio(z3, cvc5)                    # first decisive verdict wins
```

A compile error is an `error` Result written for the model, e.g. "unknown
symbol 'x' in 'x > 1'". When the target backend rejects the compiled program,
its message comes back with the numbered compiled source. A portfolio
requires its members to share an input language. It returns the first
decisive result, and `details["portfolio"]` records each member's verdict.

## Sessions: step-by-step proving

```python
lean = formalkit.backend("lean")
root = lean.start("theorem t (a b : ℕ) : a + b = b + a := by\n  sorry")
root.goals                         # ['a b : ℕ\n⊢ a + b = b + a']
s = root.apply("rw [Nat.add_comm]")
s.solved, s.proof                  # True, the complete proof file, re-checked by the kernel
root.apply("simp").solved          # states are immutable, so you can branch freely
```

A session opens at the single `sorry` in the file. Each step returns a new
`State` holding the open goals, or a failed one with the error. When no goals
remain, the backend assembles the full proof and checks it from scratch. Only
then is the state `solved`, so a closed goal list is never taken on trust.
`step_search` runs best-first search over these states.

## How backends run

* One long-lived container per backend, named `formalkit-<name>` and published on
  a random `127.0.0.1` port. Every process on the machine shares the same warm
  backend. `formalkit.backend(name)` reuses it, and `formalkit down` stops it.
* Every run gets a fresh temp directory and a hard timeout that kills the whole
  process group. Containers run with all capabilities dropped,
  `no-new-privileges`, a PID limit and a memory limit (`FORMALKIT_MEMORY`,
  default `8g`).
* To run backends elsewhere, such as another host, a compose stack or
  Kubernetes, start the image there and attach with
  `formalkit.backend("z3", url="http://host:port")`.
* `FORMALKIT_DOCKER_ARGS` passes extra `docker run` flags, for example to mount
  a Gurobi license.
* Failures are results, never exceptions, so a model can always read them.
  A malformed tool call (missing `code`, an unknown or missing input, an
  argument that isn't a string) is an `error` that says what to fix. A
  backend that hangs past its time limit is `unknown` with
  `details["timeout"]`. A crashing host-side backend is an `error` inside the
  agent. A container that dies (OOM, killed) is restarted and the run retried
  once; session states die with it.
* Concurrent first use is safe: processes that start the same backend at the
  same moment share one container. `FORMALKIT_KEEP=1` keeps the test suite
  from stopping containers that other processes are using.
* Tool names are made valid for every LLM tool API (`lean+x` becomes
  `lean_x`), and the agent and MCP server map them back.

### The wire protocol

```
GET  /health  -> {"ok": true}
GET  /spec    -> Spec
POST /run     {"code": str, "timeout": seconds, "inputs": {name: str}} -> Result

# only for backends with spec.sessions:
POST /start   {"code": str, "timeout": seconds}                -> Result (details: state, goals)
POST /step    {"state": str, "step": str, "timeout": seconds}  -> Result (details: state, goals | proof)
```

That is all a backend has to implement. Any language works, but in Python it
is one class. Session backends also implement `start` and `step`:

```python
# formalkit/adapters/mytool.py
from formalkit.core import Result, Spec, Verdict
from formalkit.server import Adapter, sh, timed_out, workdir

class MyTool(Adapter):
    spec = Spec(name="mytool", family="SMT", language="MyLang",
                emits="...", authority="...", feedback="...", use="...",
                guidance="How the model should write input and read verdicts.",
                example="...")

    def run(self, code, timeout, **inputs):
        with workdir({"input.my": code}) as d:
            proc = sh(["mytool", "input.my"], cwd=d, timeout=timeout)
        if proc.timed_out:
            return timed_out(proc)
        return Result(Verdict.PROVED if "QED" in proc.out else Verdict.ERROR, proc.out)

ADAPTER = MyTool()
```

Backends that need no container are even simpler. Subclass
`formalkit.Backend` on the host and implement `spec` and `run`, as
`compiled` and `portfolio` do. Languages that compile to an existing backend
belong in `formalkit/ir/` and are registered as virtual backends; see
`formalkit/ir/pot.py`.

For a containerized backend, add `docker/mytool/Dockerfile` (copy `docker/z3/Dockerfile`), an entry in
`formalkit/registry.py`, and example inputs named
`examples/mytool/<expected-verdict>-<label>.<ext>`. The integration tests
pick these up automatically.

## Tests

```bash
pytest -m "not docker"   # protocol, server, agent + hooks, evidence, composition, patterns, PoT compiler
pytest -m docker         # every example against its image, standard detail keys, Lean sessions, PoT on z3
```

The non-Docker tests use a scripted OpenAI-style client and in-process toy
backends (`tests/conftest.py`), so every pattern and hook is exercised
without a model or a container. Backends whose image is not built are
skipped.
