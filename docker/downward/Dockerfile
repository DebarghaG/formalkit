# Fast Downward (planner) + VAL (plan validator), both built from source.
FROM debian:bookworm-slim AS build
RUN apt-get update && apt-get install -y --no-install-recommends \
      ca-certificates git cmake g++ make python3 flex bison \
 && rm -rf /var/lib/apt/lists/*
ARG DOWNWARD_TAG=release-24.06.1
RUN git clone --depth 1 --branch ${DOWNWARD_TAG} https://github.com/aibasel/downward.git /opt/downward \
 && cd /opt/downward && ./build.py release -j"$(nproc)" \
 && rm -rf builds/release/search/CMakeFiles builds/release/search/*.o .git
ARG VAL_COMMIT=3c7a1f330bdab0ba28a4762bb45c3f06c27fb6d4
RUN git clone https://github.com/KCL-Planning/VAL.git /src/val && cd /src/val && git checkout ${VAL_COMMIT} \
 && cmake -S . -B build -DCMAKE_BUILD_TYPE=Release && cmake --build build -j"$(nproc)" \
 && mkdir -p /opt/val && find build -name 'Validate' -type f -exec cp {} /opt/val/ \; \
 && find build -name 'libVAL*.so*' -exec cp -P {} /opt/val/ \;

FROM debian:bookworm-slim
RUN apt-get update && apt-get install -y --no-install-recommends python3 \
 && rm -rf /var/lib/apt/lists/*
COPY --from=build /opt/downward/fast-downward.py /opt/downward/fast-downward.py
COPY --from=build /opt/downward/driver /opt/downward/driver
COPY --from=build /opt/downward/builds/release/bin /opt/downward/builds/release/bin
COPY --from=build /opt/val /opt/val
ENV LD_LIBRARY_PATH=/opt/val PATH=/opt/val:$PATH
COPY formalkit /opt/formalkit/formalkit
ENV PYTHONPATH=/opt/formalkit PYTHONUNBUFFERED=1
EXPOSE 8080
# Tools run unprivileged, so a program cannot damage the container it shares with later runs.
RUN useradd --create-home --uid 10001 runner
USER runner
CMD ["python3", "-m", "formalkit.server", "downward"]
