# Vampire built from source (no upstream aarch64 binaries).
FROM debian:trixie-slim AS build
RUN apt-get update && apt-get install -y --no-install-recommends \
      build-essential cmake git ca-certificates && rm -rf /var/lib/apt/lists/*
RUN git clone --depth 1 --branch v5.1.0 https://github.com/vprover/vampire /src
WORKDIR /src/build
RUN cmake .. -DCMAKE_BUILD_TYPE=Release && make -j"$(nproc)" \
 && cp "$(find . -maxdepth 2 -type f -name 'vampire*' -perm -u+x | head -1)" /usr/local/bin/vampire

FROM python:3.12-slim
COPY --from=build /usr/local/bin/vampire /usr/local/bin/vampire
COPY formalkit /opt/formalkit/formalkit
ENV PYTHONPATH=/opt/formalkit PYTHONUNBUFFERED=1
EXPOSE 8080
# Tools run unprivileged, so a program cannot damage the container it shares with later runs.
RUN useradd --create-home --uid 10001 runner
USER runner
CMD ["python3", "-m", "formalkit.server", "vampire"]
