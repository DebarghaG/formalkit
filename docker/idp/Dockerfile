# IDP-Z3 pins z3-solver==4.11.2.0 (no aarch64 wheel) and needs the Rust
# sli-lib, so wheels are built in a separate stage.
FROM python:3.12-slim AS build
RUN apt-get update && apt-get install -y --no-install-recommends build-essential cmake curl ca-certificates \
      pkg-config libclang-dev libz3-dev \
 && rm -rf /var/lib/apt/lists/*
RUN curl -sSf https://sh.rustup.rs | sh -s -- -y --profile minimal
# z3 4.11's CMakeLists predates CMake 4's minimum-version policy.
ENV PATH=/root/.cargo/bin:$PATH MAKEFLAGS=-j16 CMAKE_BUILD_PARALLEL_LEVEL=16 CMAKE_POLICY_VERSION_MINIMUM=3.5
RUN pip wheel --no-cache-dir -w /wheels idp-engine==0.12.1 \
 # z3's setup.py mislabels non-x86 Linux wheels as manylinux1, which pip rejects.
 && for w in /wheels/*-manylinux1_aarch64.whl; do [ -e "$w" ] && mv "$w" "${w%-manylinux1_aarch64.whl}-linux_aarch64.whl"; done; ls /wheels

FROM python:3.12-slim
COPY --from=build /wheels /wheels
RUN pip install --no-cache-dir --no-index -f /wheels idp-engine==0.12.1 && rm -rf /wheels
COPY formalkit /opt/formalkit/formalkit
ENV PYTHONPATH=/opt/formalkit PYTHONUNBUFFERED=1
EXPOSE 8080
# Tools run unprivileged, so a program cannot damage the container it shares with later runs.
RUN useradd --create-home --uid 10001 runner
USER runner
CMD ["python3", "-m", "formalkit.server", "idp"]
