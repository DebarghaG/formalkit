FROM python:3.12-slim
# Debian trixie: SWI-Prolog 9.2.9
RUN apt-get update && apt-get install -y --no-install-recommends swi-prolog-nox \
 && rm -rf /var/lib/apt/lists/*
COPY formalkit /opt/formalkit/formalkit
ENV PYTHONPATH=/opt/formalkit PYTHONUNBUFFERED=1
EXPOSE 8080
# Tools run unprivileged, so a program cannot damage the container it shares with later runs.
RUN useradd --create-home --uid 10001 runner
USER runner
CMD ["python3", "-m", "formalkit.server", "prolog"]
