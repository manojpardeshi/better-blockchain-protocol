"""Read-only checks of a published testnet directory against its charter registry.

    python -m testnet.preflight --registry registry.json --directory directory.json

Only GET /v0/info and GET /v0/charters/<cid> are sent. This is a configuration
and reachability check, not a safety proof or a replacement for operator drills.
"""

import argparse
import json
from urllib.parse import urlsplit

from sigil.charter import Registry
from sigil.server import RemoteStandby, RemoteWitness
from sigil.witnessd import load_registry


def _url_error(url, allow_http: bool) -> str | None:
    if not isinstance(url, str):
        return "URL must be a string"
    try:
        parsed = urlsplit(url)
        port = parsed.port  # validates the port before attempting a request
    except ValueError:
        return "malformed URL"
    if (parsed.scheme not in ("http", "https") or not parsed.hostname or parsed.username is not None
            or parsed.password is not None or parsed.path not in ("", "/") or parsed.query or parsed.fragment
            or port == 0):
        return "expected a root http(s) URL without credentials, path, query or fragment"
    if parsed.scheme == "http" and not allow_http:
        return "public directory URL must use HTTPS (use --allow-http for a local or protected testnet)"
    return None


def check(directory: dict, registry: Registry, *, timeout: float = 3.0,
          allow_http: bool = False) -> list[str]:
    """Return every configuration or endpoint mismatch; never send an admin call."""
    errors = []
    if not isinstance(directory, dict) or not isinstance(directory.get("constellations"), dict):
        return ["directory must contain a constellations object"]
    groups = directory["constellations"]
    committees = directory.get("committees", {})
    if not isinstance(committees, dict):
        return ["directory committees must be an object"]
    if not groups:
        errors.append("directory has no constellations")
    for cid in committees:
        if cid not in groups:
            errors.append(f"{cid}: committee has no constellation entry")

    used_urls = set()
    for cid, urls in groups.items():
        if not isinstance(cid, str) or not cid.isalnum():
            errors.append(f"{cid!r}: invalid constellation ID")
            continue
        charter = registry.latest(cid)
        if charter is None:
            errors.append(f"{cid}: missing verified registry chain")
            continue
        expected_chain = registry.chain(cid)
        checkpoint_required = any("checkpoint" in entry["body"] for entry in expected_chain)
        expected = [("witness", charter["witnesses"], urls)]
        committee_keys = charter.get("successor", {}).get("committee", [])
        committee_urls = committees.get(cid, [])
        if cid in committees and not committee_keys:
            errors.append(f"{cid}: directory lists a committee absent from the current charter")
        if committee_keys or cid in committees:
            expected.append(("standby", committee_keys, committee_urls))
        for role, keys, endpoints in expected:
            if not isinstance(endpoints, list):
                errors.append(f"{cid} {role}: URLs must be a list")
                continue
            if len(endpoints) != len(keys):
                errors.append(f"{cid} {role}: expected {len(keys)} URLs, got {len(endpoints)}")
            found = []
            for url in endpoints:
                bad = _url_error(url, allow_http)
                if bad:
                    errors.append(f"{cid} {role} {url!r}: {bad}")
                    continue
                if url in used_urls:
                    errors.append(f"{cid} {role} {url}: URL reused in directory")
                    continue
                used_urls.add(url)
                try:
                    client = (RemoteStandby if role == "standby" else RemoteWitness)(url, timeout=timeout)
                    info = client._info()
                    chain = client.chain(cid)
                except Exception as exc:
                    errors.append(f"{cid} {role} {url}: unreachable or malformed reply ({exc})")
                    continue
                if (info.get("role") == "standby") != (role == "standby"):
                    errors.append(f"{cid} {role} {url}: wrong daemon role")
                if info.get("constellation") != cid or info.get("version") != charter["version"]:
                    errors.append(f"{cid} {role} {url}: advertised constellation/version differs from registry")
                if info.get("pk") != client.pk:
                    errors.append(f"{cid} {role} {url}: public key changed between info reads")
                if info.get("frozen") or info.get("fenced"):
                    errors.append(f"{cid} {role} {url}: member is frozen or fenced")
                features = info.get("features")
                if checkpoint_required and ("checkpoint" not in client.features
                                            or not isinstance(features, list) or "checkpoint" not in features):
                    errors.append(f"{cid} {role} {url}: checkpointed charter requires checkpoint feature")
                if client.pk not in keys:
                    errors.append(f"{cid} {role} {url}: public key is not in current charter")
                found.append(client.pk)
                if chain != expected_chain:
                    errors.append(f"{cid} {role} {url}: served charter chain differs from registry")
            if len(found) != len(set(found)):
                errors.append(f"{cid} {role}: duplicate public key among endpoints")
            if set(found) != set(keys):
                errors.append(f"{cid} {role}: endpoint keys do not match current charter")
    return errors


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(prog="python -m testnet.preflight")
    parser.add_argument("--registry", required=True, help="agreed charter registry JSON")
    parser.add_argument("--directory", required=True, help="published network directory JSON")
    parser.add_argument("--timeout", type=float, default=3.0, help="per socket timeout in seconds")
    parser.add_argument("--allow-http", action="store_true", help="allow HTTP for a local or protected testnet")
    args = parser.parse_args(argv)
    if args.timeout <= 0:
        parser.error("--timeout must be positive")
    try:
        registry = load_registry(args.registry)
        with open(args.directory) as stream:
            directory = json.load(stream)
    except (OSError, ValueError, TypeError, KeyError, AttributeError, IndexError) as exc:
        print(f"preflight: invalid input: {exc}")
        return 1
    errors = check(directory, registry, timeout=args.timeout, allow_http=args.allow_http)
    for error in errors:
        print(f"FAIL {error}")
    if errors:
        print(f"preflight: {len(errors)} problem(s)")
        return 1
    print("preflight: directory endpoints match the verified registry")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
