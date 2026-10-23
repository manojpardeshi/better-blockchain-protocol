"""Create (on first use) and start a local testnet.

    python -m testnet.up --dir ./tn --constellations 2 --witnesses 4 [--stamps]

Witness processes are detached and keep running after this command exits;
stop them with ``python -m testnet.down --dir ./tn``. Running ``up`` again on
the same directory restarts the same witnesses on their stores and ports.
"""

import argparse
import json

from .launcher import Testnet


def main(argv=None) -> None:
    p = argparse.ArgumentParser(prog="python -m testnet.up")
    p.add_argument("--dir", default="./tn")
    p.add_argument("--constellations", type=int, default=2)
    p.add_argument("--witnesses", type=int, default=4)
    p.add_argument("--host", default="127.0.0.1")
    p.add_argument("--stamps", action="store_true", help="witnesses require a stamp per spend")
    args = p.parse_args(argv)

    tn = Testnet(args.dir, args.host)
    if not tn.witnesses:
        tn.create(args.constellations, args.witnesses, args.stamps)
    tn.stop_all()  # in case a previous run left processes behind
    try:
        tn.start_all(detach=True)
    except Exception:
        tn.stop_all()
        raise
    for cid, urls in tn.directory().items():
        print(cid)
        for u in urls:
            print("  " + u)
    print(f"directory: {tn.path('directory.json')}")
    print(f"registry:  {tn.path('registry.json')}")
    print(json.dumps({"pids": [w["pid"] for w in tn.witnesses]}))


if __name__ == "__main__":
    main()
