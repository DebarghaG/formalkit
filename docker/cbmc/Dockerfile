FROM debian:trixie-slim
# z3: an SMT backend for `// cbmc: --z3`, much faster than bit-blasting on nonlinear arithmetic.
RUN apt-get update \
 && apt-get install -y --no-install-recommends cbmc=6.6.0-4 cpp gcc libc6-dev python3 z3 \
 && rm -rf /var/lib/apt/lists/*
COPY formalkit /opt/formalkit/formalkit
ENV PYTHONPATH=/opt/formalkit PYTHONUNBUFFERED=1
EXPOSE 8080
CMD ["python3", "-m", "formalkit.server", "cbmc"]
