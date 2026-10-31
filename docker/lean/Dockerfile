# Lean 4 + Mathlib, prebuilt from the Mathlib olean cache.
# The cache is fetched over HTTP/1.1 (a temporary curl wrapper; ~/.curlrc is not reliably
# read during docker build): with many HTTP/2 streams multiplexed per connection, flaky
# networks reset streams mid-transfer (curl exit 18) faster than retries recover.
# `lake update` would run Mathlib's own one-shot `cache get` (a post-update hook);
# MATHLIB_NO_CACHE_ON_UPDATE defers it to the retry loop below.
FROM debian:bookworm-slim
ARG LEAN_VERSION=v4.35.0
ARG MATHLIB_VERSION=v4.35.0
RUN apt-get update && apt-get install -y --no-install-recommends \
      ca-certificates curl git python3 xz-utils zstd \
 && rm -rf /var/lib/apt/lists/*
ENV ELAN_HOME=/opt/elan PATH=/opt/elan/bin:$PATH
RUN curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
      | sh -s -- -y --no-modify-path --default-toolchain leanprover/lean4:${LEAN_VERSION}
WORKDIR /opt/lean-project
RUN echo "leanprover/lean4:${LEAN_VERSION}" > lean-toolchain \
 && printf 'name = "scratch"\n\n[[require]]\nname = "mathlib"\ngit = "https://github.com/leanprover-community/mathlib4"\nrev = "%s"\n' "${MATHLIB_VERSION}" > lakefile.toml \
 && printf '#!/bin/sh\nexec /usr/bin/curl --http1.1 --parallel-max 16 --retry-delay 3 "$@"\n' > /usr/local/bin/curl \
 && chmod +x /usr/local/bin/curl \
 && MATHLIB_NO_CACHE_ON_UPDATE=1 lake update \
 && { curl -s -o /dev/null -w 'mathlib cache over HTTP/%{http_version}\n' https://cache.mathlib.org/ || true; } \
 && for i in 1 2 3 4 5 6; do lake exe cache get && break; [ "$i" = 6 ] && exit 1; sleep $((i * 20)); done \
 && printf 'import Mathlib\nexample : (2 : ℕ) + 2 = 4 := by norm_num\n' > /tmp/smoke.lean \
 && lake env lean /tmp/smoke.lean \
 && rm -rf /root/.cache/mathlib /tmp/smoke.lean /usr/local/bin/curl \
 && lake env printenv LEAN_PATH > /opt/lean-project/LEAN_PATH \
 && chmod -R a+rX /opt/lean-project
# The Lean REPL powers sessions (step-by-step proving) and goals at `sorry`s.
RUN git clone --depth 1 --branch ${LEAN_VERSION} https://github.com/leanprover-community/repl /opt/repl \
 && cd /opt/repl && lake build \
 && printf '{"cmd": "theorem t (n : Nat) : n + 0 = n := by sorry"}\n\n' \
    | LEAN_PATH="$(cat /opt/lean-project/LEAN_PATH)" /opt/repl/.lake/build/bin/repl | grep -q proofState
# Final certification uses Lake's own judges (`lake comparator`, `lake check`, Lean >= 4.35), which
# build the untrusted file inside a bubblewrap sandbox. They need: bwrap; git to accept the
# root-owned Mathlib checkout when run as `checker`; Mathlib's trace files complete, so a
# read-only Mathlib replays without writing (`lake build` once here normalizes them); and a
# runtime dir. The container is started with the Docker options in formalkit/registry.py.
RUN apt-get update && apt-get install -y --no-install-recommends bubblewrap \
 && rm -rf /var/lib/apt/lists/* \
 && git config --system --add safe.directory '*' \
 && cd /opt/lean-project && lake build Mathlib > /dev/null \
 && chmod -R a+rX /opt/lean-project
# Checked files can run code at compile time (#eval, elab...). The server runs as an
# unprivileged user, so such code cannot modify the toolchain, Mathlib or the checkers.
RUN useradd --create-home --uid 10001 checker \
 && mkdir -p /run/user/10001 && chown checker /run/user/10001
COPY formalkit /opt/formalkit/formalkit
ENV PYTHONPATH=/opt/formalkit PYTHONUNBUFFERED=1 LEAN_PROJECT=/opt/lean-project LEAN_REPL=/opt/repl/.lake/build/bin/repl
USER checker
EXPOSE 8080
CMD ["python3", "-m", "formalkit.server", "lean"]
