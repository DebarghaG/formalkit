FROM debian:bookworm-slim
RUN apt-get update \
 && apt-get install -y --no-install-recommends frama-c-base why3 z3 cvc4 gcc libc6-dev python3 \
 && rm -rf /var/lib/apt/lists/* \
 && why3 config detect
COPY formalkit /opt/formalkit/formalkit
ENV PYTHONPATH=/opt/formalkit PYTHONUNBUFFERED=1
EXPOSE 8080
CMD ["python3", "-m", "formalkit.server", "framac"]
