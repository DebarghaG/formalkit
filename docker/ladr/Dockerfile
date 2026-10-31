# LADR (Prover9 + Mace4), McCune's last release, built from source.
# Serves either backend: python3 -m formalkit.server prover9|mace4
FROM debian:trixie-slim AS build
RUN apt-get update && apt-get install -y --no-install-recommends \
      build-essential curl ca-certificates && rm -rf /var/lib/apt/lists/*
RUN curl -fsSL https://www.cs.unm.edu/~mccune/prover9/download/LADR-2009-11A.tar.gz | tar xz -C /
WORKDIR /LADR-2009-11A
# Old C: tolerate modern-compiler strictness.
RUN make all CC="gcc -fcommon -std=gnu89 -Wno-error -w" \
 && mkdir -p /out && cp bin/prover9 bin/mace4 bin/interpformat bin/isofilter /out/

FROM python:3.12-slim
COPY --from=build /out/ /usr/local/bin/
COPY formalkit /opt/formalkit/formalkit
ENV PYTHONPATH=/opt/formalkit PYTHONUNBUFFERED=1
EXPOSE 8080
# Tools run unprivileged, so a program cannot damage the container it shares with later runs.
RUN useradd --create-home --uid 10001 runner
USER runner
CMD ["python3", "-m", "formalkit.server", "prover9"]
