FROM python:3.12-slim
RUN apt-get update && apt-get install -y --no-install-recommends \
      spin=6.5.2+dfsg-2 gcc libc6-dev && rm -rf /var/lib/apt/lists/*
COPY formalkit /opt/formalkit/formalkit
ENV PYTHONPATH=/opt/formalkit PYTHONUNBUFFERED=1
EXPOSE 8080
# Tools run unprivileged, so a program cannot damage the container it shares with later runs.
RUN useradd --create-home --uid 10001 runner
USER runner
CMD ["python3", "-m", "formalkit.server", "spin"]
