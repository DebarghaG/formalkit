# User-scenario evaluations

`run.py` runs the pipelines that four kinds of real users run, against a real
model and the real tools, and reports every stage separately over `k`
independent runs.

```bash
OPENAI_BASE_URL=https://api.deepseek.com OPENAI_API_KEY=... \
    python evals/run.py [researcher data_builder practitioner agent_builder] --n 8 --k 3 [--hard]
```

Each run writes every attempt and every stage to `results/<timestamp>-<model>.json`.

## Rules the suite follows

- **Fresh problems.** Names and numbers are random, so a memorized puzzle won't help.
- **Ground truth computed by code**, by brute force or true by construction.
  `tests/test_eval_generators.py` audits it. For example, every puzzle is
  re-parsed from its English text and re-solved independently, and every
  optimum is checked against an independent solver.
- **The real pipeline**, exactly as that user would call formalkit.
- **Per-stage results:**
  - `executable`: the artifact ran.
  - `decisive`: the backend reached a verdict.
  - `verified`: the pipeline claims a verified answer.
  - `faithful`: the formalization means the problem.
  - `correct`: the end answer is right.
  - `false_accept`: verified, yet wrong.
  - `pass@k` and `pass^k`: solved in at least one of k runs, and in every run.
- **A no-tools baseline** (the same model answering directly), so the lift
  from the tools is measured rather than assumed.

## Results on 2026-10-30, DeepSeek V4.1 Flash, hard level, 8 problems x 3 runs

| user | setup | correct | verified | false accepts | pass^k | notes |
|---|---|---|---|---|---|---|
| researcher | model alone | 100% | 0% | – | 100% | these puzzles don't separate the model from the pipeline |
| researcher | `Agent` over z3 + clingo | 100% | 100% | 0% | 100% | consensus of 3: 8/8 answered, 100% precision |
| practitioner | model alone | **0%** | 0% | – | 0% | 14–18 items, two capacities, dependencies |
| practitioner | `Agent` over MiniZinc, CPMpy, Pyomo | **100%** | 100% | 0% | 100% | |
| data builder | `formalize` → pinned Lean proof, true statements | 67% | 67% | 0% | 50% | all faithful; 8/12 runs yield usable data |
| data builder | same, false statements | 100% (not proved) | – | 0% | 100% | **0 "proofs" of false statements** |
| agent builder | rules in prompt, no guard | 88% | – | 12% | 75% | **4 policy violations executed** |
| agent builder | rules in prompt, `Guard` | 100% | – | 0% | 100% | 0 violations |
| agent builder | no rules in prompt, no guard | 29% | – | 62% | 25% | **15 policy violations executed** |
| agent builder | no rules in prompt, `Guard` | 96% | – | 0% | 88% | 0 violations, 13 blocks, **0 false blocks** |

What these numbers say:
- **Practitioner:** formalkit turns the model's 0% into 100%.
- **Researcher:** the answers were already right; formalkit adds verification on top.
- **Agent builder:** a guard enforces the policy that prompt rules alone don't, without blocking legitimate payments.
- **Data builder:** pinning and fidelity checks keep false statements out of the training data.

All of these numbers come from small samples (8 problems × 3 runs). They're
for regression tracking, not leaderboards.
