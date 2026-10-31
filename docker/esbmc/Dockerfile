# ESBMC has no arm64 release binaries, so build it (shared, against Debian's clang 19 and z3 4.13).
FROM debian:trixie-slim AS build
RUN apt-get update && apt-get install -y --no-install-recommends \
      build-essential ca-certificates git gperf libgmp-dev cmake ninja-build bison flex \
      libboost-all-dev libtinfo-dev python3 libz3-dev clang-19 llvm-19-dev libclang-19-dev libclang-cpp19-dev \
 && rm -rf /var/lib/apt/lists/*
# ESBMC also bundles a 32-bit libc model (for --32). On an arm64 host that
# targets 32-bit ARM, so it needs armel glibc headers (on amd64: i386 ones).
RUN if [ "$(dpkg --print-architecture)" = arm64 ]; then a=armel; else a=i386; fi \
 && dpkg --add-architecture $a && apt-get update \
 && apt-get install -y --no-install-recommends libc6-dev:$a \
 && rm -rf /var/lib/apt/lists/*
# glibc's aarch64 <bits/math-vector.h> declares SVE/NEON vector types for clang,
# which ESBMC's frontend rejects; hide them from ESBMC (it always defines __ESBMC_alloca).
RUN f=/usr/include/aarch64-linux-gnu/bits/math-vector.h; if [ -f $f ]; then \
      sed -i -e 's/^#elif __glibc_clang_prereq(8, 0)$/#elif !defined __ESBMC_alloca \&\& __glibc_clang_prereq(8, 0)/' \
             -e 's/^#if __GNUC_PREREQ(10, 0) || __glibc_clang_prereq(11, 0)$/#if !defined __ESBMC_alloca \&\& (__GNUC_PREREQ(10, 0) || __glibc_clang_prereq(11, 0))/' $f \
   && [ "$(grep -c __ESBMC_alloca $f)" = 2 ]; fi
ARG ESBMC_VERSION=v7.11
RUN git clone --depth 1 --branch ${ESBMC_VERSION} https://github.com/esbmc/esbmc /src
RUN cmake -S /src -B /build -GNinja -DCMAKE_BUILD_TYPE=Release -DBUILD_STATIC=Off -DBUILD_TESTING=Off \
      -DLLVM_DIR=/usr/lib/llvm-19/lib/cmake/llvm -DClang_DIR=/usr/lib/cmake/clang-19 \
      -DENABLE_Z3=On -DENABLE_PYTHON_FRONTEND=Off -DENABLE_SOLIDITY_FRONTEND=Off \
      -DCMAKE_INSTALL_PREFIX=/opt/esbmc \
 && cmake --build /build -j"$(nproc)" && cmake --install /build

FROM debian:trixie-slim
RUN apt-get update && apt-get install -y --no-install-recommends \
      libclang-cpp19 libllvm19 libz3-4 libgmp10 libboost-filesystem1.83.0 libboost-program-options1.83.0 \
      libboost-iostreams1.83.0 libboost-date-time1.83.0 gcc libc6-dev python3 \
 && rm -rf /var/lib/apt/lists/*
# glibc's aarch64 <bits/math-vector.h> declares SVE/NEON vector types for clang,
# which ESBMC's frontend rejects; hide them from ESBMC (it always defines __ESBMC_alloca).
RUN f=/usr/include/aarch64-linux-gnu/bits/math-vector.h; if [ -f $f ]; then \
      sed -i -e 's/^#elif __glibc_clang_prereq(8, 0)$/#elif !defined __ESBMC_alloca \&\& __glibc_clang_prereq(8, 0)/' \
             -e 's/^#if __GNUC_PREREQ(10, 0) || __glibc_clang_prereq(11, 0)$/#if !defined __ESBMC_alloca \&\& (__GNUC_PREREQ(10, 0) || __glibc_clang_prereq(11, 0))/' $f \
   && [ "$(grep -c __ESBMC_alloca $f)" = 2 ]; fi
COPY --from=build /opt/esbmc /opt/esbmc
# clang's builtin headers (stddef.h, stdarg.h, ...): without them every program that
# includes a standard header (<stdio.h>, <stdlib.h>, <pthread.h>) fails to parse.
COPY --from=build /usr/lib/llvm-19/lib/clang/19/include /usr/lib/llvm-19/lib/clang/19/include
ENV PATH=/opt/esbmc/bin:$PATH
RUN esbmc --version \
 && printf '#include <stdio.h>\n#include <stdlib.h>\n#include <string.h>\n#include <pthread.h>\nint main(void){return 0;}\n' > /tmp/h.c \
 && esbmc /tmp/h.c 2>&1 | grep -q "VERIFICATION SUCCESSFUL" && rm /tmp/h.c
COPY formalkit /opt/formalkit/formalkit
ENV PYTHONPATH=/opt/formalkit PYTHONUNBUFFERED=1
EXPOSE 8080
CMD ["python3", "-m", "formalkit.server", "esbmc"]
