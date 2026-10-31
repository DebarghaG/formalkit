"""Intermediate representations: languages compiled to a backend's language.

Each module exposes ``compile(text) -> str`` and ``backend() -> Backend``
(built with :func:`formalkit.compiled`), and is registered as a virtual
backend in :mod:`formalkit.registry`, so ``formalkit.backend("<name>")``,
the agent, MCP and the CLI can use it like any other backend.
"""
