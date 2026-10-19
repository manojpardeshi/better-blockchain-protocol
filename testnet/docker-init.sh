#!/bin/sh
# One-shot setup for docker-compose.yml: keys, genesis charter and directory
# for a constellation of $N witnesses, written once to the shared /net volume.
set -eu
N="${N:-4}"
NET="${NET:-/net}"
if [ -f "$NET/cid" ]; then
    echo "constellation $(cat "$NET/cid") already set up"
    exit 0
fi
mkdir -p "$NET/keys"
pubs=""
i=1
while [ "$i" -le "$N" ]; do
    python -m sigil.witnessd keygen --out "$NET/keys/w$i.json" > /dev/null
    pubs="$pubs $NET/keys/w$i.pub"
    i=$((i + 1))
done
# shellcheck disable=SC2086
cid=$(python -m sigil.witnessd genesis --name "${NAME:-orion}" --keys $pubs --out "$NET/registry.json")

# Directory for clients on the host (ports published by docker-compose.yml)
# and for clients on the compose network (service names).
python - "$cid" "$N" "$NET" <<'EOF'
import json, sys
cid, n, net = sys.argv[1], int(sys.argv[2]), sys.argv[3]
host = {"constellations": {cid: [f"http://127.0.0.1:{7000 + i}" for i in range(1, n + 1)]}}
inner = {"constellations": {cid: [f"http://witness{i}:7000" for i in range(1, n + 1)]}}
json.dump(host, open(f"{net}/directory.json", "w"), indent=1)
json.dump(inner, open(f"{net}/directory.internal.json", "w"), indent=1)
EOF
echo "$cid" > "$NET/cid.tmp" && mv "$NET/cid.tmp" "$NET/cid"
echo "constellation $cid"
