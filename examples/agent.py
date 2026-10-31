"""An LLM solving a problem with formal backends as its scratchpad.

    pip install 'formalkit[agent]'
    OPENAI_API_KEY=... python examples/agent.py
    # or any OpenAI-compatible server:
    OPENAI_BASE_URL=http://localhost:8000/v1 OPENAI_API_KEY=none MODEL=Qwen/Qwen3-32B python examples/agent.py
"""

import os

from openai import OpenAI

import formalkit

agent = formalkit.Agent(OpenAI(), model=os.environ.get("MODEL", "gpt-5"), backends=["z3", "clingo"])

answer = agent.solve(
    "Alice, Bob and Carol each own exactly one of a cat, a dog and a fish. "
    "Alice is allergic to fur. Bob does not own the dog. Who owns the dog?"
)
print(answer)                        # e.g.  Carol  [z3: unsat]
print(answer.verified, answer.verdict)
for step in answer.steps:            # the full, re-checkable trajectory
    print(f"--- {step.backend} -> {step.result.verdict}\n{step.arguments['code']}")
