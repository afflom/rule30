# Deterministic pinned-source intake

The existing `EnvironmentMemoryCommand.step` entrypoint additionally accepts
`r30/environment-inspection/2`. This is single-source ingestion with two required
pins: `expected_blob` (40 lowercase hexadecimal bytes) and `expected_sha256`
(64 lowercase hexadecimal bytes). The other eight fields are the v1 request
fields. Only `operation: "ingest"` is supported in v2. Missing pins, malformed
pins, unknown fields, duplicate keys and other schema versions are refused.
Existing v1 ingestion and queries retain their interface.

The command resolves the requested commit/path in the supplied local Git
repository, reads the immutable blob with the existing bounded acquisition
state machine, and compares repository, revision, path, blob and SHA-256 before
calling the existing memory writer. Content validation recomputes SHA-256 from
the exact bytes. A mismatch exits with code 2 before replacing memory. Missing
objects fail acquisition; acceptance never fetches them. A successful replay is
idempotent and still requires atomic replacement and exact validated readback.

Repository labels and caller-supplied pins do not authenticate a GitHub origin.
The response retains `observed-sources-not-proof`; source text is inert data,
never instructions or proof authority. The supplied task and sequent are not
changed. The private-directory, synchronous-driver and cleanup assumptions in
[ENVIRONMENT-PLAN.md](ENVIRONMENT-PLAN.md) apply to this same storage/acquisition
implementation. In particular, provide a private state directory and an outer
deadline, and investigate uncertain child cleanup before retrying.

## Public fixture and offline replay

The [request](../examples/environment-intake/request.json) pins this public file:

- Repository: `afflom/rule30`
- Revision: `7c76a54849b8731c729f17342fff130841b05482`
- Path: `.github/lexlean-revision`
- Git blob: `63ce6dd2ab3b7d1a214d26b8de80cfb0c67aeaf2`
- SHA-256: `64c233769fa2bbc2f53ad70cb4c7f9389a7eaa0bdd7c750f9818d8d148bdf4dc`
- Exact bytes: `9fd01c31e40bb29577833825f902fafcceedb49a` followed by LF (41 bytes).

Those bytes are also retained under their SHA-256 in
`examples/environment-intake/`. They are a non-sensitive acceptance fixture;
the command reads the pinned Git object, not the working-tree version of the
source file. The example task target is explicitly unverified.

Acquisition/refresh is a separate, explicit preparatory operation. If the pinned
commit is missing, fetch it from the public repository before acceptance:

```console
git fetch https://github.com/afflom/rule30.git 7c76a54849b8731c729f17342fff130841b05482
```

Use the generated native executable for `Rule30Api.EnvironmentMemoryCommand.step`
from `production/environment-memory-request.json` as `MEMORY_BIN`. From the Rule30
repository root, the following acceptance and replay require no network:

```sh
fixture=rule30-api/examples/environment-intake
sha256sum "$fixture/64c233769fa2bbc2f53ad70cb4c7f9389a7eaa0bdd7c750f9818d8d148bdf4dc"
git cat-file blob 7c76a54849b8731c729f17342fff130841b05482:.github/lexlean-revision |
  cmp - "$fixture/64c233769fa2bbc2f53ad70cb4c7f9389a7eaa0bdd7c750f9818d8d148bdf4dc"
state=$(mktemp -d)
timeout 30s "$MEMORY_BIN" "$state" "$fixture/request.json" > "$state/first.json"
timeout 30s "$MEMORY_BIN" "$state" "$fixture/request.json" > "$state/replay.json"
cmp "$state/first.json" "$state/replay.json"
jq '{trust, observations: (.observations | length)}' "$state/replay.json"
```

Expected: `trust` is `observed-sources-not-proof`, with one observation. Changing
either expected pin to a different well-formed hash must exit 2 and preserve
`observations.json`. Removing a pin must fail request parsing. These behaviors,
identity mismatches, content tampering and mismatched-completion refusal have
source-level obligations in `EnvironmentMemoryTraces.lex.tex`. The checked
singleton serialization equation is retained. The one new concrete-path success
example, `matchingCompletionUsesExistingAtomicWriter`, is unproved and explicitly
[deferred outside the accepted obligation set](../deferred/environment-intake/README.md).
Native writer tests are required operational evidence, not a substitute kernel
theorem. All pre-existing main obligations and runtime writer checks remain.

## Qualification and composition

Release acceptance requires pinned-compiler kernel/native qualification. Do not
treat the example or authored traces alone as accepted evidence.
Use LexLean `9fd01c31e40bb29577833825f902fafcceedb49a` with Lean 4.32.2. Start with
directed checks of `EnvironmentMemoryCommand` and `EnvironmentMemoryTraces`,
then the unchanged repository gate and native production request. Keep timing
and peak-memory logs outside the attested tree; run expensive jobs sequentially.

Both intake modules are existing entrypoints and catalog scopes. The catalog
reads the command's `features` definition, which includes pinned acceptance.
The supporting closed-goal fixture proof repair registers 29 proof-only
`ClosedGoalJsonData`, `ClosedGoalJsonSteps*` and `ClosedGoalJsonFixtures` modules
in `lexlean.toml` and regenerates its lock. It preserves the exact fixture wire,
public claims and axiom policies while factoring checked decoding and matching
through shared functions. Runtime production roots and model registration are
unchanged. `lexlean.toml`, `ResearchCatalog.lex.tex`, `model/` and
`production/request.json` remain shared composition paths to reconcile.

The separation follows `afflom/me` commit
`414941a2a93565a8f68bef134445e1c6c3ef469a`: explicit refresh, deterministic
acceptance over pinned local inputs. Rule30 already uses local/vendored inputs
and exact-input proof caches; this change does not claim to fix repeated
normative network fetches in its proof gate.
