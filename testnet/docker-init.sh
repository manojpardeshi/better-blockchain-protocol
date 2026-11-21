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
    key="$NET/keys/w$i.json"
    pub="$NET/keys/w$i.pub"
    if [ -e "$NET/registry.json" ] && [ ! -e "$key" ] && [ ! -L "$key" ]; then
        echo "$key is missing while registry.json exists; refusing to replace a witness identity" >&2
        exit 1
    fi
    if [ -e "$key" ] || [ -L "$key" ]; then
        # An interrupted init may have written the key before cid. Keep that
        # identity and restore only a missing public file.
        python3 - "$key" "$pub" <<'PY'
import os
import sys
from sigil.witnessd import load_key

key, pub = sys.argv[1:]
pk = load_key(key).pk
if os.path.lexists(pub):
    with open(pub) as f:
        published = f.read().strip()
    if published != pk:
        raise SystemExit(f"{pub}: does not match {key}; refusing to replace either file")
else:
    with open(pub, "x") as f:
        f.write(pk + "\n")
PY
    elif [ -e "$pub" ] || [ -L "$pub" ]; then
        echo "$pub exists without $key; refusing to replace either file" >&2
        exit 1
    else
        python3 -m sigil.witnessd keygen --out "$key" > /dev/null
    fi
    pubs="$pubs $NET/keys/w$i.pub"
    i=$((i + 1))
done
# shellcheck disable=SC2086
cid=$(python3 -m sigil.witnessd genesis --name "${NAME:-orion}" --keys $pubs --out "$NET/registry.json")

# Directory for clients on the host (ports published by docker-compose.yml)
# and for clients on the compose network (service names).
python3 - "$cid" "$N" "$NET" <<'EOF'
import json, sys
cid, n, net = sys.argv[1], int(sys.argv[2]), sys.argv[3]
host = {"constellations": {cid: [f"http://127.0.0.1:{7000 + i}" for i in range(1, n + 1)]}}
inner = {"constellations": {cid: [f"http://witness{i}:7000" for i in range(1, n + 1)]}}
json.dump(host, open(f"{net}/directory.json", "w"), indent=1)
json.dump(inner, open(f"{net}/directory.internal.json", "w"), indent=1)
EOF
echo "$cid" > "$NET/cid.tmp" && mv "$NET/cid.tmp" "$NET/cid"
echo "constellation $cid"
