# A Sigil witness daemon (python -m sigil.witnessd). See testnet/README.md.
FROM python:3.12-slim

RUN pip install --no-cache-dir "cryptography>=41" \
 && useradd --create-home --uid 10001 sigil \
 && mkdir -p /net /data \
 && chown sigil:sigil /net /data

WORKDIR /app
COPY sigil/ sigil/
COPY testnet/ testnet/

USER sigil
ENV PYTHONUNBUFFERED=1
# Witness state lives here; mount a volume so it survives the container.
VOLUME ["/data"]
EXPOSE 7000
ENTRYPOINT ["python", "-m", "sigil.witnessd"]
CMD ["--help"]
