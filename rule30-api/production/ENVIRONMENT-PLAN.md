# Explicit environmental-memory plans

`EnvironmentPlanCommand.step` accepts a bounded corpus through one native Host
command. It supplements the unchanged single-source v1 command. It acquires
observations and returns context; it does not synthesize proofs, crawl GitHub,
or schedule Engine learning.

The executable takes `PRIVATE_STATE_DIRECTORY REQUEST.json`. The caller must
provide a private state directory and an outer execution deadline: lock acquisition
is blocking. Ingestion requires caller-owned local Git repositories. Query needs
only the store and a plan; it never opens those repositories.

The private directory reserves `git-output`, `git-errors`, `store.lock`,
`observations.pending`, and `observations.json`. These paths must not be symlinks
or hardlink aliases of one another or of other files. No competing writer or
adversarial filesystem mutation may touch them during an operation; cooperative
command callers must use the same lock. Inspect retained state and establish
child termination before retrying when cleanup is uncertain. Scratch-file changes
are not a store transaction, and an outer deadline does not establish cleanup.

The native Host driver handles requests synchronously. The pure step function
rejects incompatible event variants, but it does not authenticate arbitrary
forged or replayed responses of the expected variant. Its event protocol assumes
the owned synchronous driver; it is not an authenticated external event service.

The request schema is `r30/environment-plan/1` with exactly these fields:

- `spec`, `operation` (`ingest` or `query`), `task`, `query`, `sources`.
- `task` is the existing complete ready `Research.Task` request shape.
- `query` contains 1–128 bytes.
- `sources` contains 1–8 entries, in retrieval order.
- Each entry has `repository` (claimed owner/name), `revision` (40 lowercase
  hexadecimal bytes), and `path` (1–256 safe relative-path bytes).
- Ingestion entries additionally require `local_repository`, a nonempty printable
  ASCII path of at most 1024 bytes. Query entries omit that field entirely.

Unknown or duplicate JSON fields, invalid entries, and repeated source keys are
refused. A source key is the exact repository/revision/path triple. Repeating it
with a different local directory is also refused. The entire plan is validated
before locking or starting Git, including entries later in the list.

See `../examples/environment-plan-ingest.json` and
`../examples/environment-plan-query.json`. These are caller-adaptable examples,
not proof requests or successful acquisition receipts. Supply the actual local
checkout paths for ingestion. The example task's unverified target stays unverified.

The command holds the existing store lock and runs `EnvironmentAcquisition`
sequentially, preserving its no-network Git command, exact commit/path/blob
binding, ownership rules, and 4096-byte **whole-file** cap. It accumulates validated
observations in memory. A later acquisition failure or capacity/conflict refusal
performs no store replacement, retaining the prior `observations.json` bytes.
Git output scratch files may have changed and must remain private.

Only after all acquisitions succeed does it serialize once, write
`observations.pending`, rename it over `observations.json`, and require exact
validated readback before success. An unconfirmed replacement or readback is
reported as uncertain. No power-loss durability or fsync guarantee is claimed.
The existing store format, 32-record capacity and 1 MiB serialization/readback
bound are unchanged. Already-known observations remain idempotent.

Both operations return `r30/environment-context/1` with the unchanged task and
sequent, the `observed-sources-not-proof` trust label, and at most eight matching
observations. Only exact keys listed in the plan are eligible; results follow
plan order, independently of store order. Missing keys and nonmatching content
produce no observation; another revision or unselected path cannot substitute.
Repository labels do not authenticate a GitHub origin. Source text stays inert
and has no proof authority.

The production request is `environment-plan-request.json`, selecting only the
new `Rule30Api.EnvironmentPlanCommand.step` export. Official verification still
covers every configured obligation. This source increment is awaiting independent
review and kernel/native qualification; linked-IR checking alone is not acceptance.
