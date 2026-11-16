# Future public compiler candidate qualification

Prepared only: no candidate has been fetched, built, adopted, or qualified.
The known-failing native path has not been rerun. The accepted application
branch remains clean at `fb41d36a7409bb9fa6b7b80efd6c191ff94446b4` (PR #17).

## Executor readiness, 2026-11-16

- `/workspace`: about 51 GiB free; installed compiler checkout/build 3.1 GiB,
  installed Lean toolchain 2.8 GiB, accepted gate cache 1.4 GiB.
- Container limit: 16 GiB RAM, no swap, four CPU equivalents
  (`cpu.max = 400000 100000`). Host reports about 16 GiB available, but the
  container limit is the operative bound. Run one heavy workload at a time.
- `/tmp` is a separate 8.8 GiB mount. Use
  `TMPDIR=/workspace/r30-pr13-candidate-tmp` for future builds and gates.
- No active Lean/compiler/gate workload was found at preparation time. Recheck
  capacity and process activity immediately before qualification.
- Rust/Cargo 1.97.1, Git 2.52.0, Lean 4.32.1 are installed.
- Read-only `git ls-remote` to public `https://github.com/afflom/lexlean.git`
  succeeded. This confirms public Git access, not candidate acceptance.

Pinned toolchain paths are under
`/workspace/.setup/elan/toolchains/leanprover--lean4---v4.32.1/bin`.
Lean commit: `f054605aea4b840552cca2e725580bffd1e1b704`.

| Tool | SHA-256 |
|---|---|
| lean | e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550 |
| lake | 60330ab6f07dce20f3fa9ebb08e8b984ea9549eac172afeb15d9d2227060e2b3 |
| leanchecker | c7c51e296d28dd443ed60f9414feef41253ede89dea76dbb2adde29768c3ed5f |
| baseline LexLean | 6deb44b3873c4ca23156dae7ee04708d92e66b5bac8354d868261365ffaaa87c |

Use the existing verified Tini subreaper at
`/workspace/r30-pr13-tools/tini-amd64 -s --` around hooks/native execution;
PID 1 does not reap test descendants reliably. This changes no hooks.

## Entry condition and acquisition

Wait for the compiler owner/parent to identify the fully integrated, reviewed
PUBLIC commit, including canonical compile, replay, and audit integration and
regression results. A partial resolver patch does not satisfy this condition.
The minimum consumer contract is below. Verify the candidate's required Lean
toolchain against the installed one before building; a different requirement
is a new qualification constraint, not permission to substitute tools.

Once that condition is met, ordinary Git fetch from the public origin is
feasible in the existing clean compiler checkout. Resolve and record the exact
fetched commit, create a distinct detached worktree, and build with `--locked`
and a separate `CARGO_TARGET_DIR` under `/workspace`. Preserve baseline
`eadeff7cfe5c8e127b26543da04bfc2352d89047` and its binary. No credential,
private package, held receipt, or source-transfer bundle is needed.

## Minimal consumer contract

1. Language 1.2 native-core source, semantic snapshots, bounded `inspect`, exact
   tool/semantic identities, and `LexLeanStd.Host` executable production remain
   available. `ResearchCohortCommand.step` must export to certified `rust-std`.
2. Generated and imported modules may share `Rule30UOR` while having distinct
   full module names. Compilation, replay and audit must use the same
   identity-bound resolved objects; declaration and receipt identities remain
   exact. Full-name collisions must fail closed.
3. Missing generated objects must not fall back to imported lookalikes. Root
   selection, object hashes, canonical path containment, transitive imports,
   and server/private object companions must be validated. Preserve original
   imported libraries and deterministic evidence/provenance.
4. Keep `Rule30UOR.*` research registration, the strict receipt rules,
   constructive application/research axiom policies, and all repository hooks.
   Compiler certificate axioms remain governed by the compiler's existing
   separate policy; do not misreport them as application declarations.
5. A new compiler binary/semantics identity needs fresh matching locks, request
   pins, exports, and gate evidence. Old accepted evidence remains baseline
   evidence only. No composed main/v0.2 pin is selected by this harness.

## Ordered qualification sequence

1. Read candidate instructions and run its directed shared-namespace tests.
   Unpack `/workspace/r30-pr13-replay-repro.tar.gz` into a NEW directory.
   Run the two-project reproducer with the candidate. Require full verify
   success, not only a raw checker or merged-directory diagnostic. Record
   compiler SHA, semantics, tool hashes, attestation and process evidence.
   Exercise the missing-local-object, full-name collision, wrong identity,
   containment/symlink and transitive/companion regressions in the upstream
   supported harness. No application gate until these pass.
2. Create an isolated consumer qualification branch from accepted PR #17.
   Only there bind the reviewed candidate pin, refresh the three compiler
   locks and generated API metadata through existing commands. Include the
   supplied LexLean fixture, generate its host Lean with that compiler, and
   register it through `bin/r30 module add NativeAcceptanceFixture`. Never
   edit generated Lean by hand. Run unchanged full hooks once for this batch.
   Keep the accepted public corrective branch and main untouched.
3. Export the selected cohort executable from the same consumer source using
   `cohort-production-request.json`; verify/replay the bundle and build its
   copied package offline. Record the source/semantic/build/attestation/bundle
   identities and executable hash. If the candidate changes the certified
   target descriptor, obtain and review its official descriptor; do not reuse
   the baseline target digest blindly.
4. Create a fresh local bare origin with `receive.denyNonFastForwards=true` and
   a fresh fixture clone. Push the hook-accepted fixture commit to local main
   through the unchanged pre-push hook. Retain every old failed workspace and
   the original protected origin. Never force-push public branches.
5. Derive a NEW request from `baseline-request.json` using ordinary JSON data
   transformation, not a new runtime. Replace repository, exact fixture commit
   and tree, compiler semantics and all four actual tool digests; choose fresh
   output/error/journal paths outside owned workspaces. Keep one supplied
   `claim:problem1` / `problem1` premise task, source
   `Rule30UOR.NativeAcceptanceFixture.premise`, premise index 2, budget 1 and
   max_quarantined 1. Incoming goal arenas stay empty for owned inspection.
   Do not run the baseline request unchanged: it identifies preserved data.
6. Run the regenerated executable with the qualified tools on PATH, exact
   `LEXLEAN_BIN`, workspace-backed `TMPDIR`, external telemetry and Tini.
   Permit its ordinary owned inspection, synthesis, verification, renamed
   source verification, host/theorem registration, commit/push hooks and
   cleanup; no injected receipts or manual advancement.
7. Positive assertions: checked proof has allowed exact axioms; publication
   commit/evidence are nonempty only after acknowledged push; local remote
   main equals the reported commit; generation record is sealed; owned
   workspace is released after acknowledgement; no compiler build cache is
   tracked. This premise proof is a supporting lemma: `problem1` remains open.
   Preserve exact result, journal, commit tree, remote ref, logs, bundle and
   tool identities.
8. After positive acceptance advances local origin, run a second fresh bounded
   request against the OLD fixture predecessor with fresh serial/journal/log
   paths. The existing exact-revision push lease must refuse the stale
   predecessor; non-fast-forward server protection remains enabled. Assert
   remote head unchanged, no published commit/evidence acknowledged for this
   refused batch, and owned recovery workspace retained. Do not rewrite the
   remote or modify a hook to create the refusal. Record actual native outcome.
9. Report each gate and native receipt against its exact compiler/application
   head. Remote CI is separate; do not equate local hooks with remote CI. Send
   results to the parent for composed-pin/integration review. No release,
   main merge or production pin adoption is implied by local qualification.

## Preserved baseline evidence

- Accepted app source: `/workspace/rule30-pr13-corrections`, clean at
  `fb41d36a7409bb9fa6b7b80efd6c191ff94446b4`.
- Accepted API attestation:
  `ebbfa109438062348ccf5ff6be8b1323dd703d244078859e601c75de4489c56f`.
- Native bundle:
  `a612b1428bb6520cf11628e04e10d1f359d50f9affbfa2a828e28cb09c072a1d`.
- Native binary SHA:
  `3f4d0f0300eb2f6fa3796919bb7705e6de247c428d06a06756242de03568a696`.
- Failed end-to-end result and exact request:
  `/workspace/r30-pr13-evidence/native-case-2/`.
- Retained failed workspace:
  `/workspace/r30-pr13-native-fixture-2/.r30/research/ab796a50df2443bc1e48351a4d1a542c3579365c-128`.
- Reproducer archive SHA:
  `3445227332bf1531eca724984a386c41883abec38a2f57b2548d57682faba74f`.

The distinct-namespace experiment is diagnostic only and is not an acceptance
path. No known-failing native execution or full gate was rerun during this
harness preparation.
