# Independent operator testnet: readiness runbook

This is a checklist for a **testnet with no real value**. It describes what an
operator must arrange around the current witness daemon; it is not a deployment
template or a claim that the protocol is ready for public funds. Start with the
[local multi-process testnet](../testnet/README.md) to learn the commands.
The repository's [Docker Compose file](../docker-compose.yml) is a local fixture:
one volume holds *all* witness keys, and its witnesses disable rate limiting.
Do not publish those containers on an open network.

## Before inviting outside operators

1. **Agree on membership and control.** Each witness gets a distinct Ed25519
   key and a distinct operator, host, storage volume and administrative
   credential. Exchange only the `.pub` files for genesis. Check that the
   generated charter contains exactly the agreed public keys and threshold
   before distributing its constellation ID and registry. A second
   constellation should have independent operators too; several witnesses
   controlled by one person are not independent fault domains.
2. **Plan the network boundary.** `sigil.witnessd` serves HTTP, including
   operator calls. Bind it to loopback or a private interface, and put an
   authenticated, TLS protected transport in front of it before giving clients
   an outside URL. Keep the path from that transport to the daemon private.
   Publish `https://` URLs for Python wallets and `RemoteNetwork` in the
   client directory only after testing them from another host. Do not send an
   admin bearer token across plain HTTP.
   Restrict access to `/v0/freeze`, `/v0/adopt`, `/v0/settled`,
   `/v0/standby`, `/v0/succeed` and `/v0/probe` at the network boundary as
   well as with each daemon's own `--admin-token FILE`. These operator calls
   are exempt from its request rate limit; some can freeze or fence a member.
3. **Isolate state.** Put each private key, admin token and durable store in
   storage readable only by its operator process. Keep the store on persistent
   storage; a vote is written before it is returned. Protect the registry and
   directory against accidental changes, and record the key, constellation ID,
   charter version, store path and public endpoint for each member.
4. **Set an abuse budget.** On a non-loopback bind, the Python daemon defaults
   to 20 requests per second per observed client with a burst of 100. Do not
   pass `--rate-limit 0` to an exposed daemon unless the front end enforces
   its own limits. A reverse proxy can make every request appear to come from
   one address; apply limits at the proxy and review
   [admission control](WIRE.md#admission-control). The current
   `--stamps` flag does not establish pricing: `/v0/sell_stamp` will
   blind-sign for any caller.
5. **Agree on recovery before startup.** Back up private keys, wallet data
   and registry material securely. A witness store is a safety record, not
   replaceable cache. **Never start a witness with its old key and a missing or
   stale store**: it could sign a conflicting vote. If the store is lost,
   quarantine that key and arrange a rotation while the remaining current
   members still have a quorum. If they do not, stop and investigate; the
   protocol does not promise recovery from a lost quorum.

## Bootstrap one witness

The steps below use the Python reference daemon. Operators run these on their
own machines; the coordinator collects only public keys. This is a command
outline, not a service manager or TLS configuration.

```sh
python -m sigil.witnessd keygen --out /private/w1.json
# Share /private/w1.pub with the other operators; never share w1.json.
```

`keygen` refuses to replace an existing private key or its `.pub` file in both
the Python and Rust CLIs. Keep the key and its public file together; if a run
stops after creating only the private key, derive its public key from that key
instead of running `keygen` again. Replacing a witness key can make its durable
store unusable and remove that member from the constellation.

After all public keys are agreed, create and compare the same genesis registry
and constellation ID. The coordinator can run:

```sh
python -m sigil.witnessd genesis --name orion \
  --keys w1.pub w2.pub w3.pub w4.pub --out registry.json
```

Each operator verifies that registry, sets `CID` to its verified constellation
ID, and runs only their own key and store:

```sh
python -m sigil.witnessd run --key /private/w1.json \
  --registry registry.json --constellation "$CID" \
  --store /persistent/w1.db --host 127.0.0.1 --port 7000 \
  --admin-token /private/w1-admin-token
```

The token file must contain a nonempty secret. The daemon checks it for
operator calls; it does not provision the file or protect the network. If
rotation will not be exercised, omitting `--admin-token` disables those calls.
Serve the local daemon through the separately configured protected transport.
Create a directory mapping `<cid>` to each operator's reachable `https://`
URL, following [the wire format](WIRE.md#files). A successor committee needs
its own independent keys, stores, endpoints and `committees` entry; see
[succession](WIRE.md#succession). The local Compose fixture has no committee.

Before publishing that directory, run the read-only endpoint check from a
separate host using the agreed registry and the exact directory clients will
receive:

```sh
python -m testnet.preflight --registry registry.json --directory directory.json
```

For a dated evidence file, add `--report-json preflight-report.json`. The
report records the result, redacted error codes, and SHA-256 hashes of the
exact registry and directory bytes it read. A hash is `null` if that file
could not be read. Keep the input files alongside the report for later review;
the report intentionally omits endpoint URLs and public keys. The option does
not change the command's normal terminal diagnostics or exit status.

It validates the registry chain, requires HTTPS URLs, and checks that every
registry and directory JSON object has unique keys, so the recorded inputs are
unambiguous. It checks that every
current witness (and, when configured, standby member) has a unique endpoint
and public key, announces the expected constellation and charter version, and
serves the exact agreed chain. If any charter in the chain uses a checkpoint,
it also requires every current witness and standby member to advertise the
`checkpoint` feature. It exits nonzero and reports each mismatch.
For a local testnet or protected private HTTP transport, pass `--allow-http`.
The check only reads `/v0/info` and `/v0/charters/<cid>`; it does not test
admin access controls, TLS termination policy, payment liveness, or independent
operator control. Run the acceptance drills below as well.

### Rust standby heartbeat endpoints

The Rust `sigil-witness standby` heartbeat client currently accepts only
`http://` URLs. This applies to `--members URL ...` with `--probe-every S`
and to URLs passed to its admin `/v0/probe` call. Those member URLs must be
**private HTTP endpoints carried over an operator-controlled protected network
or tunnel**, with the witness listener inaccessible from the public Internet.
Keep the public wallet directory on HTTPS; it describes different endpoints
for a different client. Supplying the directory's HTTPS URLs to a Rust standby
will make its heartbeat probes fail, potentially causing a false dead-man
observation. Do not substitute publicly reachable plain HTTP URLs.

`RemoteNetwork.probe` sends the directory's member URLs to `/v0/probe`.
Therefore it cannot be used as a liveness check for a Rust standby in this
split-endpoint setup. For an operator check, call that standby's admin
`/v0/probe` without `urls`; it uses the private `--members` list and returns
`answered`. The Python standby uses
`urllib.request` and can probe HTTPS URLs. This limitation remains until the
Rust heartbeat client supports TLS.

## Testnet acceptance drills

Record the results and the charter/daemon version used:

- From a separate host, fetch each member's `/v0/info` and
  `/v0/charters`. Confirm the advertised public key, constellation ID and
  charter version match the agreed registry. Confirm the published transport
  validates its certificate and a request to an admin path without its token
  is refused.
- Make payments between independent wallet processes and between at least
  two constellations. Verify the received dossier from a separately operated
  client. Include a failed or timed-out request and its recovery path.
- Kill one witness during payment, restart it on **the same store**, and
  check that earlier votes and payments still verify. Exercise a partition
  and observe that payment completion can stop when a quorum is unavailable.
- Rehearse rotation with real operators and unique tokens, including registry
  distribution after the new charter is signed. A rotation is not complete
  merely because the old members froze: new members must adopt the evidence.
  Practice the partial-rotation recovery below.
  If using succession, test standby mirrors, probes and handover separately.
- Confirm operator processes can be monitored for health and disk exhaustion.
  The reference daemon has no packaged metrics, alerting, service manager,
  backup procedure or TLS termination; the testnet deployment must supply
  and verify these.

### Recover a partial rotation

If `RemoteNetwork.rotate` reports that too few current witnesses or standby
members signed, some old members may already be frozen, even if their FREEZE
replies were lost. Restore their reachability on the same stores, then retry on
the **same `RemoteNetwork`
object**, for the same parent charter, successor keys and endpoints, committee
keys and endpoints, `dead_man` period and `compact` setting. That object keeps
the original successor body and checkpoint for the retry. Creating a new object
can produce a different charter hash if `/v0/settled` answers have changed;
members already frozen for the first hash will refuse it.

If `rotate` raises `RotationIncomplete`, the signed version is already in force;
finish its pending adoption instead of proposing another rotation. Keep the
signed chain from the operator's registry, the handover snapshots from
`RemoteNetwork.last_handover`, and the exception's `checkpoint`. Bring pending
new witnesses or standby members back on their original keys and stores,
gossip the signed chain to them, and complete `/v0/adopt` or `/v0/standby` with
those snapshots and that same checkpoint. A re-used key whose old process did
not sign must first provide its own evidence by FREEZE for the **same signed
successor**; include that evidence in its handover. The
[local chaos runner](../tests/integration/chaos/run.py) demonstrates recovery
for pending witnesses. Distribute the new registry and directory after the
adoption is complete.

Keep this testnet at no real value while the independent operation, incident
response, economics and external audit items in the [roadmap](ROADMAP.md#phase-5-public-testnet-and-audit-12)
remain open.
