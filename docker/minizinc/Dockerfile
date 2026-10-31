# Official MiniZinc image (multi-arch): Gecode, Chuffed, OR-Tools CP-SAT, HiGHS, COIN-BC.
FROM minizinc/minizinc:2.9.3
RUN apt-get update && apt-get install -y --no-install-recommends python3 \
 && rm -rf /var/lib/apt/lists/*
COPY formalkit /opt/formalkit/formalkit
ENV PYTHONPATH=/opt/formalkit PYTHONUNBUFFERED=1
EXPOSE 8080
CMD ["python3", "-m", "formalkit.server", "minizinc"]
