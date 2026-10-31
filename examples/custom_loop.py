"""Bring your own agent loop: backends are plain tools for any LLM SDK.

Shown with the Anthropic Messages API; `tool("openai")` and `tool("mcp")`
give the other formats.
"""

import anthropic

import formalkit

lean, z3 = formalkit.backends("lean", "z3")
tools = {b.name: b for b in (lean, z3)}

client = anthropic.Anthropic()
messages = [{"role": "user", "content": "Prove in Lean 4 that for all natural numbers n, n + 0 = n."}]
while True:
    resp = client.messages.create(
        model="claude-opus-5-5",
        max_tokens=4096,
        tools=[b.tool("anthropic") for b in tools.values()],
        messages=messages,
    )
    messages.append({"role": "assistant", "content": resp.content})
    calls = [c for c in resp.content if c.type == "tool_use"]
    if not calls:
        break
    messages.append({
        "role": "user",
        "content": [
            {"type": "tool_result", "tool_use_id": c.id, "content": tools[c.name].call(c.input).feedback()}
            for c in calls
        ],
    })
print(resp.content[-1].text)
