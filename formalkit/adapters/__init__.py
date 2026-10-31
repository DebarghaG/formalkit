"""Container-side adapters, one module per backend.

Each module defines ``ADAPTER``, an instance of
:class:`formalkit.server.Adapter`. Adapters import their tool's Python
packages lazily (inside ``run``) or call its binary, so this package can be
imported anywhere.
"""
