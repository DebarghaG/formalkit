FROM python:3.12-slim
RUN apt-get update && apt-get install -y --no-install-recommends tini && rm -rf /var/lib/apt/lists/*
RUN pip install --no-cache-dir cpmpy==1.1.1 ortools==9.15.6755 numpy==2.5.4
COPY formalkit /opt/formalkit/formalkit
ENV PYTHONPATH=/opt/formalkit PYTHONUNBUFFERED=1
EXPOSE 8080
# tini reaps orphaned grandchildren (Ultimate's JVMs, processes a user script forks); the Python
# server as PID 1 would leave them as zombies until the container's PID limit is exhausted.
ENTRYPOINT ["tini", "-s", "--"]
CMD ["python3", "-m", "formalkit.server", "cpmpy"]
