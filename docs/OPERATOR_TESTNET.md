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
   Publish `https://` URLs in the client directory only after testing them
   from another host. Do not send an admin bearer token across plain HTTP.
   Restrict access to `/v0/freeze`, `/v0/adopt`, `/v0/standby`,
   `/v0/succeed` and `/v0/probe` at the network boundary as well as with
   each daemon's own `--admin-token FILE`. These calls can freeze or fence
   a member and are exempt from its request rate limit.
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
rotation calls; it does not provision the file or protect the network. If
rotation will not be exercised, omitting `--admin-token` disables those calls.
Serve the local daemon through the separately configured protected transport.
Create a directory mapping `<cid>` to each operator's reachable `https://`
URL, following [the wire format](WIRE.md#files). A successor committee needs
its own independent keys, stores, endpoints and `committees` entry; see
[succession](WIRE.md#succession). The local Compose fixture has no committee.

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
  If using succession, test standby mirrors, probes and handover separately.
- Confirm operator processes can be monitored for health and disk exhaustion.
  The reference daemon has no packaged metrics, alerting, service manager,
  backup procedure or TLS termination; the testnet deployment must supply
  and verify these.

Keep this testnet at no real value while the independent operation, incident
response, economics and external audit items in the [roadmap](ROADMAP.md#phase-5-public-testnet-and-audit-12)
remain open.
