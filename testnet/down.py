"""Stop every witness of a local testnet (SIGTERM, then SIGKILL after 10 s).

    python -m testnet.down --dir ./tn

Keys, stores and the directory are kept: ``testnet.up`` restarts the same
network. Delete the directory to start over.
"""

import argparse

from .launcher import Testnet


def main(argv=None) -> None:
    p = argparse.ArgumentParser(prog="python -m testnet.down")
    p.add_argument("--dir", default="./tn")
    args = p.parse_args(argv)
    tn = Testnet(args.dir)
    if not tn.witnesses:
        raise SystemExit(f"no testnet in {args.dir}")
    tn.stop_all()
    print(f"stopped {len(tn.witnesses)} witnesses")


if __name__ == "__main__":
    main()
