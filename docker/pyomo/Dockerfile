# Pyomo with HiGHS (LP/MILP/convex QP). gurobipy runs under its size-limited
# restricted license out of the box; mount a full license with e.g.
#   FORMALKIT_DOCKER_ARGS="-v /path/gurobi.lic:/opt/gurobi/gurobi.lic:ro -e GRB_LICENSE_FILE=/opt/gurobi/gurobi.lic"
FROM python:3.12-slim
RUN apt-get update && apt-get install -y --no-install-recommends tini && rm -rf /var/lib/apt/lists/*
RUN pip install --no-cache-dir pyomo==6.10.1 highspy==1.15.1 gurobipy==13.0.3 numpy==2.5.4
# scipy: needed by the gurobi_direct interface
RUN pip install --no-cache-dir scipy==1.18.1
COPY formalkit /opt/formalkit/formalkit
ENV PYTHONPATH=/opt/formalkit PYTHONUNBUFFERED=1
EXPOSE 8080
# tini reaps orphaned grandchildren (Ultimate's JVMs, processes a user script forks); the Python
# server as PID 1 would leave them as zombies until the container's PID limit is exhausted.
ENTRYPOINT ["tini", "-s", "--"]
CMD ["python3", "-m", "formalkit.server", "pyomo"]
