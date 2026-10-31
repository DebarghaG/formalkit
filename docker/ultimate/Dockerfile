# Ultimate Automizer is Java, but its release bundles x86-64 SMT solver binaries.
# We drop those and put native z3/cvc5 on PATH instead, so the image builds on
# both amd64 and arm64 (MathSAT has no arm64 build; the default configs don't need it).
FROM debian:trixie-slim
RUN apt-get update \
 && apt-get install -y --no-install-recommends openjdk-21-jre-headless z3=4.13.3-1 cvc5 python3 tini curl ca-certificates unzip gcc libc6-dev \
 && rm -rf /var/lib/apt/lists/*
ARG ULTIMATE_VERSION=v0.3.1
RUN curl -fsSL -o /tmp/ua.zip https://github.com/ultimate-pa/ultimate/releases/download/${ULTIMATE_VERSION}/UltimateAutomizer-linux.zip \
 && unzip -q /tmp/ua.zip -d /opt && rm /tmp/ua.zip \
 && cd /opt/UAutomizer-linux && rm -f z3 cvc4 mathsat ltl2ba \
 && ln -s /usr/bin/z3 z3 && ln -s /usr/bin/cvc5 cvc5 \
 # The launcher asks for a 15G heap; size it to the container instead.
 && sed -i 's/"-Xmx15G"/"-XX:MaxRAMPercentage=75"/' Ultimate.py \
 && chmod -R a+rwX /opt/UAutomizer-linux
# Eclipse only resolves the SWT fragment for x86_64; Ultimate needs its classes
# (not its native GUI code), so let OSGi resolve x86_64 fragments on any arch.
RUN sed -i 's/"-Xms4m",/"-Xms4m", "-Dosgi.arch=x86_64",/' /opt/UAutomizer-linux/Ultimate.py \
 && grep -q osgi.arch /opt/UAutomizer-linux/Ultimate.py
COPY formalkit /opt/formalkit/formalkit
ENV PYTHONPATH=/opt/formalkit PYTHONUNBUFFERED=1
EXPOSE 8080
# tini reaps orphaned grandchildren (Ultimate's JVMs, processes a user script forks); the Python
# server as PID 1 would leave them as zombies until the container's PID limit is exhausted.
ENTRYPOINT ["tini", "-s", "--"]
CMD ["python3", "-m", "formalkit.server", "ultimate"]
