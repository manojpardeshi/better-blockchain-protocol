# Local testnet

A real Sigil network on one machine: every witness is its own
`python -m sigil.witnessd` process with its own durable store, reached only
over HTTP ([wire protocol v0](../docs/WIRE.md)).

## Processes

From the repository root (requires `pip install cryptography`):

```bash
python -m testnet.up   --dir ./tn --constellations 2 --witnesses 4   # create + start
python -m testnet.down --dir ./tn                                     # stop (SIGTERM)
python -m testnet.up   --dir ./tn     # restart the same witnesses on their stores and ports
rm -rf ./tn                           # start over
```

`up` creates the directory on first use and prints each constellation id with its witness URLs. Witnesses are detached and keep running until `down`. Add `--stamps` to make witnesses require a [stamp](../sigil/stamps.py) with every spend.

```
tn/
  keys/<name>-<i>.json   witness private keys (mode 0600); .pub alongside
  data/<name>-<i>.db     witness stores (SQLite WAL); *.stamps.json with --stamps
  logs/<name>-<i>.log    witness output
  registry.json          charter registry
  directory.json         network directory: {"constellations": {cid: [url, ...]}}
  testnet.json           launcher state (ports, pids)
```

Using it from Python:

```python
import json
from sigil import Wallet
from sigil.server import RemoteNetwork
from sigil.swap import atomic_swap

directory = json.load(open("tn/directory.json"))["constellations"]
net = RemoteNetwork(directory)              # charters are fetched and verified
orion, lyra = list(directory)
alice, bob = Wallet("alice", net, orion), Wallet("bob", net, lyra)
usd, gold = alice.issue("USD", 1000), bob.issue("GOLD", 10)
alice.pay(bob, usd, 250)
atomic_swap(alice, usd, 100, bob, gold, 2)
```

Crash a witness and bring it back (it must remember every vote it gave):

```bash
kill -9 <pid from tn/testnet.json>
python -m testnet.up --dir ./tn          # restarts all witnesses, on the same stores and ports
```

`tests/test_testnet.py` does all of this automatically, including a SIGKILL during payments.

## The witness daemon

`testnet` is a thin wrapper around `sigil.witnessd`, which you can also run by hand:

```bash
python -m sigil.witnessd keygen  --out w1.json            # also writes w1.pub
python -m sigil.witnessd genesis --name orion --keys w1.pub w2.pub w3.pub w4.pub --out registry.json
python -m sigil.witnessd run --key w1.json --registry registry.json \
    --constellation <cid printed by genesis> --store w1.db --port 7001
```

`run` verifies every charter chain in the registry, then restores the witness from its store, or joins the constellation on first start, and serves until SIGTERM/SIGINT. Each vote is committed to the store before it is sent, so the daemon can be killed at any point.

## Docker

`docker-compose.yml` at the repository root runs one 4-witness constellation, one container per witness:

```bash
docker compose up -d --build
docker compose run --rm --entrypoint cat init /net/directory.json > directory.json   # host URLs 127.0.0.1:7001-7004
docker compose kill -s SIGKILL witness2 && docker compose start witness2           # crash + restart
docker compose down            # keeps keys and stores; `down -v` wipes them
```

A one-shot `init` service (`testnet/docker-init.sh`) writes the keys, the genesis charter and the directory files into a shared `net` volume. Each witness keeps its store in its own volume (`data1` to `data4`). `directory.internal.json` lists the URLs for clients inside the compose network.

For a testnet only: all private keys sit in one shared volume. A real deployment gives each witness only its own key.
