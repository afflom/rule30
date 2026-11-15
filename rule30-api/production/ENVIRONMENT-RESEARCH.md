# Supplied context for one research attempt

`EnvironmentResearchCommand.step` is a native Host entry. Export it with
`environment-research-request.json`, then call the generated executable with
one request filename. `environment-research-example.json` is a complete wire
example with illustrative identities, NOT evidence of a verified attempt.
Replace its library tree, revision, tool digests and paths with actual inputs.
No source or proof is acquired or synthesized by this command.

## Admission

The request is `r30/environment-research/1`, with exactly `spec`, `plan`,
`context`, and `candidates`. The plan is an existing QUERY
`r30/environment-plan/1` object; it carries the entire task, nonempty query
and 1–8 explicit source triples. The context is the unchanged
`r30/environment-context/1` envelope, including its exact
`observed-sources-not-proof` trust label. It need not contain every planned
source: observations must form a unique ordered subsequence of the plan.
Every observed content must match the query. The existing observation validator
checks claimed repository/path/commit/blob formats, acquisition label, nonempty
whole content of at most 4 KiB, and its SHA-256 digest. None of these checks
authenticates a GitHub origin or a supplied Git object.

The whole original request is at most 8 MiB with the existing depth-96 JSON
parser. Duplicate keys, including escaped duplicates, are refused recursively.
Embedded object budgets are measured on canonical JSON, not original whitespace:
plan at most 64 KiB with its existing depth-16 parser; context at most 1 MiB
with depth 16. This is a stricter overall depth limit for nested candidate
requests than parsing each candidate at depth 96 independently. Work limits
also apply; a request inside byte limits may still be refused.

There are 1–16 candidates, each exactly `{cue, attempt}`. A cue contains
1–128 UTF-8 bytes. Each attempt is a full supplied `r30/research-attempt/1`;
synthesis and premise goals are refused. `CandidateBinding.selectedClosed`
requires the named constant, origin equal to theorem, zero premise, empty
telescope, origin membership in sources and exact goal binding. The serialized
target is parsed under the candidate bounds, requires exactly nodes/root, and
passes the existing pure core renderer over every node, including unreachable
nodes and nested fields. Rendered validation bytes are discarded; the supplied
config and target bytes remain unchanged. Valid unused nodes and nonzero roots
are supported. Large well-shaped unused nodes can exhaust the existing work or
output budget; no validation limit is enlarged. Every candidate,
including every unselected candidate, passes `ResearchFactory.candidateReady`:
workspace/tool bounds and pure source construction across the complete arena.
This checks shape and applicability, never proof success. A well-formed invalid
proof must still fail in the owned verifier.

Task comparison explicitly compares every field, reusing the existing purpose,
ordered-source and sequent comparisons: id, purpose,
intent, status, component, ordered sources, schema, all six sequent fields,
age and weight. Every candidate request has the same full task, serial and
snapshot. `ResearchProject.sameWorkspace` and `ResearchFactory.sameTools`,
plus full request equality and maxBytes/maxDepth/maxSteps equality, preserve
all workspace, environment, tool and execution bounds. Candidate arena, proof,
imports, levels and allowed constructive axioms may differ; the winner is
passed unchanged. The same process environment is supplied to every parser.
The snapshot's `library` is a Git TREE identity; workspace and observation
`revision` fields are COMMIT identities. They are not equated.

## Selection and lifecycle

Each candidate scores one hit per admitted observation containing its cue,
from zero to eight. The highest score wins; earlier input order breaks ties.
No observations or all-zero scores picks index zero and reports fallback.
Source text and cue bytes are only substring data. They never supply commands,
imports, tools, proof terms or goals. Candidate proof data comes solely from
the explicit attempts, under the existing construction and verification checks.

Only after the entire input and pool pass admission does the command call
`ResearchSession.begin` once. It retains the selected session and selection
metadata, with no alternative pool for retries. There is no memory-store
access or lock acquisition. Acquisition and query must finish in another
process before supplying the envelope; the inherited Host has no unlock call.

Output is `r30/environment-research-result/1`: `selection` contains policy
`r30/context-cue-count/1`, context authority
`supplied/self-consistent/not-authenticated`, SHA-256 of the ORIGINAL request
bytes (an audit binding, not authority), chosen zero-based index, score,
matched zero-based observation indices and fallback. `result` preserves the
existing `r30/research-result/1` request/status/detail/evidence fields; blocked
results include the existing recovery workspace. Admission failure has empty
selection metadata. Only an owned session completion can produce a checked
outcome, after verification and evidence retention. A failed selected proof
never starts a second attempt and does not refute or exhaust the task.

The Host driver is synchronous. `ResearchSession.Event.cancel` is an internal
pure event, not a native external cancellation channel. This command forwards
native replies as host events; it does not invent a cancellation input.
Incompatible events are refused by the owning lifecycle; arbitrary forged or
replayed same-variant events are not authenticated by the pure model.

The caller must enforce a whole-run deadline. Timeout, OS termination or crash
does not establish descendant termination or completed cleanup. Inspect retained
workspace, processes and evidence before retrying. A crash after evidence
archival but before output remains uncertain; there is no automatic retry,
durable scheduler, exactly-once, restart or power-loss guarantee. Use the
existing owned-workspace safety assumptions and do not reuse an uncertain
workspace. Context is never proof authority, source inspection or autonomous
learning. This increment does not incorporate the separate inspector work.

## Qualification boundary

Source/frontend checks and focused diagnostics precede independent review.
Full-profile production, exact generated executable acceptance, the normal
commit gate and exact-head CI remain required. The compiler is the existing
fixed-kernel native candidate, not an assertion of upstream acceptance.
