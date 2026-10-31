# AlphaGeometry's symbolic engine only (DD+AR): no language model, no jax.
# Two upstream fixes: a headless matplotlib backend, and check_cyclic's tuple
# unpacking bug ("(a, b, c), *ps = points"), which crashed every numeric check
# of a cyclic goal.
FROM python:3.10-slim
ARG AG_COMMIT=6777cb586cbb46beed28db12dc72c69770b68337
RUN apt-get update && apt-get install -y --no-install-recommends curl ca-certificates \
 && curl -fsSL https://github.com/google-deepmind/alphageometry/archive/${AG_COMMIT}.tar.gz | tar xz -C /opt \
 && mv /opt/alphageometry-${AG_COMMIT} /opt/alphageometry \
 && sed -i "s/matplotlib.use('TkAgg')/matplotlib.use('Agg')/" /opt/alphageometry/numericals.py \
 && sed -i "s/  (a, b, c), \*ps = points/  a, b, c, *ps = points/" /opt/alphageometry/numericals.py \
 && grep -q "  a, b, c, \*ps = points" /opt/alphageometry/numericals.py \
 && apt-get purge -y curl && apt-get autoremove -y && rm -rf /var/lib/apt/lists/*
# Versions pinned by AlphaGeometry's requirements.txt.
RUN pip install --no-cache-dir absl-py==1.4.0 numpy==1.23.5 scipy==1.10.0 matplotlib==3.7.0
COPY formalkit /opt/formalkit/formalkit
ENV PYTHONPATH=/opt/formalkit PYTHONUNBUFFERED=1 MPLBACKEND=Agg ALPHAGEOMETRY=/opt/alphageometry
EXPOSE 8080
# Tools run unprivileged, so a program cannot damage the container it shares with later runs.
RUN useradd --create-home --uid 10001 runner
USER runner
CMD ["python3", "-m", "formalkit.server", "ddar"]
