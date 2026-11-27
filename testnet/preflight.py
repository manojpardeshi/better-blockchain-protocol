"""Read-only checks of a published testnet directory against its charter registry.

    python -m testnet.preflight --registry registry.json --directory directory.json

Only GET /v0/info and GET /v0/charters/<cid> are sent. This is a configuration
and reachability check, not a safety proof or a replacement for operator drills.
"""

import argparse
from datetime import datetime, timezone
import hashlib
import json
import math
import os
import tempfile
from urllib.parse import urlsplit

from sigil.charter import Registry
from sigil.server import RemoteStandby, RemoteWitness


def _unique_json(data: bytes):
    """Reject ambiguous operator inputs, including duplicate keys in nested objects."""
    def unique_pairs(pairs):
        obj = {}
        for key, value in pairs:
            if key in obj:
                raise ValueError(f"duplicate JSON key: {key}")
            obj[key] = value
        return obj

    return json.loads(data, object_pairs_hook=unique_pairs)


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

    used_endpoints = set()
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
                parsed = urlsplit(url)
                # Root URLs with a slash, host case changes, or an explicit
                # default port still address the same daemon.
                endpoint = (parsed.scheme, parsed.hostname,
                            parsed.port or (443 if parsed.scheme == "https" else 80))
                if endpoint in used_endpoints:
                    errors.append(f"{cid} {role} {url}: URL reused in directory")
                    continue
                used_endpoints.add(endpoint)
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


_ERROR_CODES = (
    ("directory must contain", "invalid_directory"),
    ("directory committees must be", "invalid_committees"),
    ("directory has no constellations", "empty_directory"),
    ("committee has no constellation entry", "orphan_committee"),
    ("invalid constellation ID", "invalid_constellation_id"),
    ("missing verified registry chain", "missing_registry_chain"),
    ("directory lists a committee absent", "unexpected_committee"),
    ("URLs must be a list", "invalid_endpoint_list"),
    (" URLs, got ", "endpoint_count_mismatch"),
    ("URL reused in directory", "reused_endpoint_url"),
    ("unreachable or malformed reply", "endpoint_unreachable_or_malformed"),
    ("wrong daemon role", "wrong_daemon_role"),
    ("advertised constellation/version differs", "wrong_constellation_or_version"),
    ("public key changed between info reads", "unstable_public_key"),
    ("member is frozen or fenced", "frozen_or_fenced_member"),
    ("checkpointed charter requires checkpoint feature", "missing_checkpoint_feature"),
    ("public key is not in current charter", "unexpected_public_key"),
    ("served charter chain differs", "charter_chain_mismatch"),
    ("duplicate public key among endpoints", "duplicate_public_key"),
    ("endpoint keys do not match", "endpoint_keys_mismatch"),
)


def _report_error(error: str) -> str:
    """Reduce a diagnostic to a code; never copy untrusted URLs or replies."""
    if "URL must be a string" in error or "malformed URL" in error or "expected a root http(s) URL" in error or "public directory URL must use HTTPS" in error:
        return "invalid_endpoint_url"
    return next((code for marker, code in _ERROR_CODES if marker in error), "check_failed")


def _write_report(path: str, *, registry_hash: str | None, directory_hash: str | None,
                  errors: list[str]) -> None:
    report = {
        "schema_version": 1,
        "checked_at_utc": datetime.now(timezone.utc).isoformat(timespec="seconds").replace("+00:00", "Z"),
        "success": not errors,
        "errors": errors,
        "registry_sha256": registry_hash,
        "directory_sha256": directory_hash,
    }
    # Replace atomically so an interrupted run cannot leave a partial report.
    directory = os.path.dirname(os.path.abspath(path))
    temp_path = None
    try:
        with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8", dir=directory,
                                         prefix=".preflight-", suffix=".json", delete=False) as stream:
            temp_path = stream.name
            json.dump(report, stream, indent=2)
            stream.write("\n")
        os.replace(temp_path, path)
    finally:
        if temp_path is not None and os.path.exists(temp_path):
            os.unlink(temp_path)


def _read_inputs_with_hashes(registry_path: str, directory_path: str):
    """Parse the same bytes whose hashes are recorded in the evidence report."""
    hashes = [None, None]
    contents = []
    first_error = None
    for index, path in enumerate((registry_path, directory_path)):
        try:
            with open(path, "rb") as stream:
                data = stream.read()
            hashes[index] = hashlib.sha256(data).hexdigest()
            contents.append(_unique_json(data))
        except (OSError, ValueError, TypeError) as exc:
            contents.append(None)
            if first_error is None:
                first_error = exc
    return contents, hashes, first_error


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(prog="python -m testnet.preflight")
    parser.add_argument("--registry", required=True, help="agreed charter registry JSON")
    parser.add_argument("--directory", required=True, help="published network directory JSON")
    parser.add_argument("--timeout", type=float, default=3.0, help="per socket timeout in seconds")
    parser.add_argument("--allow-http", action="store_true", help="allow HTTP for a local or protected testnet")
    parser.add_argument("--report-json", metavar="PATH", help="write a redacted JSON evidence report")
    args = parser.parse_args(argv)
    if not math.isfinite(args.timeout) or args.timeout <= 0:
        parser.error("--timeout must be a positive finite number")
    if args.report_json and os.path.exists(args.report_json):
        if any(os.path.samefile(args.report_json, path)
               for path in (args.registry, args.directory) if os.path.exists(path)):
            parser.error("--report-json must not overwrite an input file")
    hashes = [None, None]
    try:
        if args.report_json:
            contents, hashes, read_error = _read_inputs_with_hashes(args.registry, args.directory)
            if read_error is not None:
                raise read_error
        else:
            contents = []
            for path in (args.registry, args.directory):
                with open(path, "rb") as stream:
                    contents.append(_unique_json(stream.read()))
        registry = Registry()
        for cid, chain in contents[0].items():
            registry.add_chain(cid, chain)
        directory = contents[1]
    except (OSError, ValueError, TypeError, KeyError, AttributeError, IndexError) as exc:
        print(f"preflight: invalid input: {exc}")
        if args.report_json:
            try:
                _write_report(args.report_json, registry_hash=hashes[0],
                              directory_hash=hashes[1], errors=["invalid_input"])
            except OSError as report_exc:
                print(f"preflight: report write failed: {report_exc}")
        return 1
    errors = check(directory, registry, timeout=args.timeout, allow_http=args.allow_http)
    for error in errors:
        print(f"FAIL {error}")
    if args.report_json:
        try:
            _write_report(args.report_json, registry_hash=hashes[0],
                          directory_hash=hashes[1], errors=[_report_error(error) for error in errors])
        except OSError as exc:
            print(f"preflight: report write failed: {exc}")
            return 1
    if errors:
        print(f"preflight: {len(errors)} problem(s)")
        return 1
    print("preflight: directory endpoints match the verified registry")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
