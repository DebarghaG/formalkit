# Isabelle/HOL from the official image (HOL heap and ATPs for Sledgehammer included).
# aarch64 hosts use the _ARM tag; on x86_64 build with
#   --build-arg ISABELLE_TAG=Isabelle2026
ARG ISABELLE_TAG=Isabelle2026_ARM
FROM makarius/isabelle:${ISABELLE_TAG}
USER root
RUN ln -sf /home/isabelle/Isabelle/bin/isabelle /usr/local/bin/isabelle \
 && command -v python3
USER isabelle
# No-op when the bundled HOL heap is current; guarantees fast startup otherwise.
# HOL-Library is prebuilt too, so theories may import "HOL-Library.Name".
RUN isabelle build -b HOL && isabelle build -b -j 4 HOL-Library
COPY formalkit /opt/formalkit/formalkit
ENV PYTHONPATH=/opt/formalkit PYTHONUNBUFFERED=1
EXPOSE 8080
ENTRYPOINT []
CMD ["python3", "-m", "formalkit.server", "isabelle"]
