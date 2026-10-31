FROM python:3.12-slim
ARG CVC5_VERSION=1.4.2
ADD https://github.com/cvc5/cvc5/releases/download/cvc5-${CVC5_VERSION}/cvc5-Linux-arm64-static.zip /tmp/cvc5-arm64.zip
ADD https://github.com/cvc5/cvc5/releases/download/cvc5-${CVC5_VERSION}/cvc5-Linux-x86_64-static.zip /tmp/cvc5-x86_64.zip
RUN python3 - <<'PY'
import os, platform, shutil, stat, zipfile
arch = {"aarch64": "arm64", "arm64": "arm64"}.get(platform.machine(), "x86_64")
with zipfile.ZipFile(f"/tmp/cvc5-{arch}.zip") as z:
    member = next(n for n in z.namelist() if n.endswith("bin/cvc5"))
    with z.open(member) as src, open("/usr/local/bin/cvc5", "wb") as dst:
        shutil.copyfileobj(src, dst)
os.chmod("/usr/local/bin/cvc5", 0o755)
for f in os.listdir("/tmp"):
    if f.endswith(".zip"):
        os.remove(os.path.join("/tmp", f))
PY
RUN cvc5 --version | head -1
COPY formalkit /opt/formalkit/formalkit
ENV PYTHONPATH=/opt/formalkit PYTHONUNBUFFERED=1
EXPOSE 8080
CMD ["python3", "-m", "formalkit.server", "cvc5"]
