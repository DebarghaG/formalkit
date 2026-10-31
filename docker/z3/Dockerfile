FROM python:3.12-slim
RUN pip install --no-cache-dir z3-solver==5.3.3.0
COPY formalkit /opt/formalkit/formalkit
ENV PYTHONPATH=/opt/formalkit PYTHONUNBUFFERED=1
EXPOSE 8080
CMD ["python3", "-m", "formalkit.server", "z3"]
