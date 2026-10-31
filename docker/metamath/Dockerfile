# metamath-exe (the reference verifier) + a pinned set.mm for `$[ set.mm $]`.
FROM debian:bookworm-slim AS build
ARG METAMATH_VERSION=v0.198
RUN apt-get update && apt-get install -y --no-install-recommends ca-certificates gcc libc6-dev curl \
 && rm -rf /var/lib/apt/lists/*
RUN curl -sSfL https://github.com/metamath/metamath-exe/archive/refs/tags/${METAMATH_VERSION}.tar.gz | tar xz \
 && cd metamath-exe-* && gcc -O2 -o /usr/local/bin/metamath *.c -lm

FROM debian:bookworm-slim
ARG SETMM_COMMIT=a155669326c0bcbca1d6ce8460dac0b6a8961a97
RUN apt-get update && apt-get install -y --no-install-recommends ca-certificates curl python3 \
 && mkdir -p /opt/metamath \
 && curl -sSfL -o /opt/metamath/set.mm https://raw.githubusercontent.com/metamath/set.mm/${SETMM_COMMIT}/set.mm \
 && apt-get purge -y curl && apt-get autoremove -y && rm -rf /var/lib/apt/lists/*
COPY --from=build /usr/local/bin/metamath /usr/local/bin/metamath
COPY formalkit /opt/formalkit/formalkit
ENV PYTHONPATH=/opt/formalkit PYTHONUNBUFFERED=1 METAMATH_LIB=/opt/metamath
EXPOSE 8080
CMD ["python3", "-m", "formalkit.server", "metamath"]
