FROM python:3.12-slim
# Debian trixie: kissat 4.0.2, drat-trim 2024-04-28
RUN apt-get update && apt-get install -y --no-install-recommends kissat=4.0.2-1 drat-trim \
 && rm -rf /var/lib/apt/lists/*
COPY formalkit /opt/formalkit/formalkit
ENV PYTHONPATH=/opt/formalkit PYTHONUNBUFFERED=1
EXPOSE 8080
CMD ["python3", "-m", "formalkit.server", "kissat"]
