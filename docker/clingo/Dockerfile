FROM python:3.12-slim
# `python3 -m clingo` is the full clingo application.
RUN pip install --no-cache-dir clingo==5.8.2
COPY formalkit /opt/formalkit/formalkit
ENV PYTHONPATH=/opt/formalkit PYTHONUNBUFFERED=1
EXPOSE 8080
# Tools run unprivileged, so a program cannot damage the container it shares with later runs.
RUN useradd --create-home --uid 10001 runner
USER runner
CMD ["python3", "-m", "formalkit.server", "clingo"]
