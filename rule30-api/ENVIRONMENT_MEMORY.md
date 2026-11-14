# Bounded environmental memory

`EnvironmentMemoryCommand.step` is a native LexLean Host entry for a bounded,
local environmental-memory inspection. It acquires a file from an exact local
Git commit, retains the observation, reopens and validates the store, and returns
relevant source context alongside the caller's unchanged `Research.Task`.

This is a usable acquisition/retrieval interface, not autonomous Engine learning,
GitHub crawling, or an integration with the unpublished source inspector.

## Run

Build the production root with the project's qualified compiler and unchanged
acceptance policy:

```
lexlean production build --project rule30-api/lexlean.toml \
  --request rule30-api/production/environment-memory-request.json
```

Use the generated `rule30_environment_memory` executable from that certified
bundle. It takes exactly two arguments: an existing private state directory and
a request JSON file. Run from the repository root for the example's `.` source:

```
mkdir -m 700 /tmp/r30-memory-example
rule30_environment_memory /tmp/r30-memory-example \
  rule30-api/examples/environment-inspection.json
```

The example selects the public main snapshot's Host abstraction and searches for
`Request`. Its task target is explicitly an unverified interface fixture. Replace
the entire `task` with a real caller-owned task before using the returned context
in research. The command does not resolve, inspect, or prove that task's goal.

For a later process, keep the same state directory and change `operation` to
`query`. The local source need not exist for a query. Keep all eight request keys;
`local_repository` and `path` can be empty strings for a query. Change `query` to
another nonempty, case-sensitive byte substring (at most 128 bytes). An unrelated
query or a different exact revision returns no observations, not stale context.

## Versioned interface

Input `r30/environment-inspection/1` has exactly these keys: `spec`, `operation`
(`ingest` or `query`), `local_repository`, `repository`, `revision`, `path`,
`query`, and `task`. The existing `ResearchInput.task` decoder admits the task;
all its fields, including every contextual-sequent field, are returned unchanged.

Output `r30/environment-context/1` contains `task`, `observations`, and the fixed
trust label `observed-sources-not-proof`. Each observation has the claimed GitHub
`repository` label, exact `revision`, `path`, locally resolved Git `blob`, raw
`content`, SHA-256 `digest`, and `acquisition: local-git-object`.

The source owner/repository label is a claim supplied by the caller. The command
does not authenticate GitHub ownership or prove that the commit is published
there. Local acquisition establishes a commit/path/blob relation through fixed
Git commands and checks content length before retention. On disk, even matching
digests and acquisition labels are untrusted records, not authentication receipts.

The later source inspector can consume the observations as search hints for the
same supplied task. It must inspect any proposed declaration against its owned
snapshot and exact goal, then use the existing kernel/axiom gates. This command
constructs neither `Research.ResultKind.inspected` nor `checked`, changes no
registered claim, and never executes text or instructions from observations.

## Bounds and ownership

- One ingestion acquires one SHA-1 Git commit/path, at most 4 KiB of content.
  SHA-256-format Git repositories are explicitly unsupported in this increment.
- Fixed Git invocations resolve `COMMIT^{commit}:PATH`, read the resolved object's
  size, then read exactly that blob. No shell, textconv, filters, hooks, replace
  objects, lazy fetch, credential prompts, or network protocol is enabled.
- Each of the three Git jobs has a 10-second allowance and bounded poll count.
- At most 32 observations are retained. Duplicate keys/content are idempotent;
  changed revisions remain separate; conflicting content for an existing
  repository/revision/path is refused. A full store is refused, never evicted.
- Both serialized stores and readback are limited to 1 MiB, including escaped
  JSON. Requests are limited to 64 KiB. Retrieval returns at most eight records.
- The caller owns a dedicated private state directory and source repository.
  There must be no competing writer or adversarial filesystem mutation. The
  existing Host lock blocks on contention; this interface does not claim a
  bounded lock-acquisition timeout. Do not share the state directory with
  unrelated tools or place symlinks at its fixed filenames.
- `store.lock`, `git-output`, `git-errors`, `observations.pending`, and
  `observations.json` are reserved in that directory. Source data never selects
  paths or executable arguments outside the validated source identity.

## Persistence and failures

A writer locks the directory's store lock, validates any prior store, writes a
canonical pending file, renames it over the store, then reads and validates the
exact bytes again. Only successful readback produces context output with exit 0.
A malformed prior store is never overwritten. Interrupted/failed pending writes
must not be called learned memory. Keep the private directory after an uncertain
rename/readback or child-cleanup error and inspect it before retrying.

This provides process-restart persistence, not a power-loss durability guarantee:
Host does not expose fsync. Host reads are preceded by size checks for caller
files; those checks rely on the private-path/no-adversarial-mutation assumption.

## Acceptance

Use the generated executable, not a handwritten substitute, to check:

1. Ingest the pinned example, compare returned blob with local Git resolution,
   digest with acquired bytes, and every task/sequent field with the input.
2. End that process. Query in a new process; obtain the same observation.
3. Repeat ingestion; retain exactly one record. Change query or revision; obtain
   no old context. Ingest a changed fixture commit; retain both revisions.
4. Reject malformed JSON, duplicate or unknown fields, forged content digests,
   conflicting immutable keys, excessive content/store budgets, and path escape.
5. Attempt writes with an obstructed pending or destination path. Require failure
   and no successful learned/context output; preserve the prior valid store.
6. Ingest a fixture containing hostile instructions; return it only as observed
   data. Exercise worst-case JSON escapes and reopen the result.

Kernel traces cover core retrieval, idempotence, revision separation, malformed
records, round-trip readback, escaped-size budget and unchanged exact task. Native
acceptance and the full repository gate must be reported separately; neither a
parse/link check nor a fixed-kernel test-only manifest is main's acceptance.
