# Working in this repository

This file is for anyone, human or agent, who changes the proof surfaces. It is
short on purpose: the commands below return compact reports, so a session can
act on them without reading build logs.

## The one rule

LexLean is the only authoring surface for new implementation and proof-surface
changes. `rule30-core-lean/Rule30UOR` retains the host proof library; its presence
does not authorize new handwritten Lean or runtime code. New logic and proof
candidates belong in `.lex.tex` source and must pass the unchanged gate.

When publishing an existing or generated Lean declaration into the paper,
use `bin/r30 theorem add`: it generates the glossary entry and statement and
elaborates the probe used by `lexlean verify`. Never hand-edit a glossary entry
to make an unsupported statement appear representable. A retained host lemma
that LexLean cannot state remains host evidence until the language can express
it; new application logic still belongs in LexLean.

Every theorem depends on at most `propext` and `Quot.sound`. `Classical.choice`
is forbidden: `by_cases` on an undecidable proposition is a compile error, and
`cfomega` is `omega` without classical preprocessing (`Rule30UOR.Constructive`).

## The loop

Start a session with `bin/r30 brief`: one screen with the open claims (the only
places to work), the proved reductions (equivalent forms of the goal; use them,
do not re-derive them), the refuted routes (do not walk them again) and the
loop below. `bin/r30 claim <id>` gives one claim in full: register entry, Lean
type, published statement, dependents. Neither requires reading STRATEGY.md,
which is the historical log.

```
bin/r30 brief                          # the session briefing
bin/r30 claim <id> [--related]         # one claim in full; --related lists the theorems about its constants
bin/r30 chain                          # the reduction tree of the register: what rests on what, with status
bin/r30 interface <id> [--write]       # the labeled interface sheet of a claim (chain, notions, exact facts, handles); --write puts it in interfaces/
bin/r30 view render [--out <dir>]      # the stakeholder view (site, artifacts) that the view workflow publishes; the runtime of Presentation.lex.tex
bin/r30 api sync | check               # regenerate / drift-check the LexLean API modules, the PrismPM model and the logo
bin/r30 api production                 # export the production roots of Api.lex.tex to certified Rust (lexlean production) and replay the bundle
bin/r30 status                         # HEAD, dirty files, frontier counts
bin/r30 frontier list                  # what is open, proved, refuted
bin/r30 lexicon search <text>          # find lexemes by id, surface, or Lean name
bin/r30 sig <Lean names>               # a declaration's type as an s-expression
bin/r30 mentions <Lean constants>      # every theorem whose statement mentions all of them: what is already proved about a notion
bin/r30 module add <Name> [--build]    # register (and create) a research module: Lake root + axiom-audit import
bin/r30 module build [<Names>]         # lake build; prints only errors
bin/r30 unpublished <module prefixes>  # theorems without a lexeme, and whether they can be published
bin/r30 theorem preview <Lean names>   # the entry and statement, without writing
bin/r30 theorem add <Lean names>       # write entry + statement, lock, check the module, probe
bin/r30 define <Lean definitions>      # publish each notion's defining equation as a lemma in the Notions section
bin/r30 theorem remove <qids>          # unpublish: delete the entry and its statement block, lock (one lexeme per Lean constant)
bin/r30 check paper --modules src/Observations.lex.tex   # seconds
bin/r30 verify paper --modules src/Observations.lex.tex  # seconds; the real probe
bin/r30 axioms <Lean names>            # must print only propext, Quot.sound
bin/r30 frontier check                 # the register against the kernel (also run by the gate)
bin/r30 choice-audit                   # theorems depending on Classical.choice (must be none)
bin/r30 commit -m "..." [--push]       # commit through the pre-commit gate, in the background
bin/r30 gate                           # is that gate still running; its last stage and log tail
bin/r30 experiment run <name> [args]   # a finite diagnostic on the seed
bin/r30 sequences [--write]            # the basis of the map (Sequences.lex.tex); --write evaluates it in Lean
bin/r30 discover [--write]             # induction: relations and recurrences of the basis, certified; --write records them as observed
```

Costs: `check`/`verify` of one module take seconds; `verify` of the whole paper
takes about six minutes (`Paper.lex.tex` is 13k lines). The pre-commit gate
runs everything (tooling tests, Lean build, vacuity and axiom audits, kernel
replay, bridge, both LexLean projects, PDFs) but reuses the last accepted run's
Lake build directories and any LexLean verification whose exact inputs were
already accepted, so a commit that touches one research module and
`Observations.lex.tex` takes a few minutes; the first run after a toolchain
change takes twenty to thirty. Use the module forms while iterating and the
gate once per batch.

`--json` on any command gives the same report as JSON. The same commands are
available as MCP tools: `claude mcp add r30 -- python3 <repo>/tools/r30/mcp_server.py`.
The tool list is derived from the CLI parser (`cli.build_parser`): adding a
subcommand adds a tool, with its arguments as the input schema, and no
endpoint is registered by hand. The API is also written in LexLean:
`rule30-api/src/Api.lex.tex` is a semantic module declaring the command
surface as data (`Argument`, `Command`, `commands`) with a kernel-checked
count theorem; `bin/r30 api sync` regenerates it from the parser, `api check`
(run by the tests) refuses a parser that drifted from it, and the gate
verifies the module with `lexlean` like the paper. LexLean emits Lean for it
and, through `bin/r30 api production` (`lexlean production`, SPEC §24.7),
certified Rust packages of its production roots (`commands`, `commandCount`),
kernel-checked and replayed, into `rule30-api/.lexlean/production/` (never
committed); the PrismPM registers `errors`, `dependencies`, `runtime-roots`
and `stdlib-package`, the result schemas, the Gherkin suites and
`CONFORMANCE.md` are generated and drift-checked with the modules.
`rule30-api/src/Architecture.lex.tex` (on the vendored prism-stdlib `Foundation.Arch` and `Foundation.Qual`: stakeholders, concerns, viewpoints, views, and the quality model that defines an optimal implementation), `Presentation.lex.tex` and `Application.lex.tex` (the stakeholder view and its publication, whose runtime is `bin/r30 view render`) are generated the same way; the PrismPM model lives in `rule30-api/model/` and `prismpm.toml`.
`rule30-api/src/Register.lex.tex` is the register in the same form: the
claims of `frontier.toml` as data, with the well-formedness of the plan
(every `depends` target is a claim, every proved claim names a Lean theorem)
as theorems the kernel decides. `frontier add|set` and `api sync` regenerate
it; `api check` refuses drift.

## No Python: LexLean only

Python is deprecated in this repository, and so is any other hand-written runtime (the owner,
2026-11-01: "No more python. LexLean only. PrismPM helps." "LexLean compiles to rust, so we do not
need shell scripts or whatever. Use LexLean."). The implementation is authored in LexLean, using
prism-stdlib, and runs as the Rust that `lexlean production` generates from it; PrismPM governs
the registers. Never add a `.py` file or a shell script, and never extend `tools/r30`,
`scripts/*.py` or the shell glue: the pre-commit authoring policy refuses a commit that adds a
Python file or grows the Python it touches, with no bypass.

The development compiler pinned in `.github/lexlean-revision` follows `release/v0.5`.
LexLean PR #396 supplies the actual PR #389 `LexLeanStd.Host` interface; PR #439
adds a generated executable entry for a root with the native Host step signature,
explicit file/process effects, and owned child cleanup. The API imports these
types directly; `Rule30Api.Host` is the application harness. Use this compiler
to complete the native application and remove legacy glue as each replacement
passes the gate. Ordinary pure roots still export as libraries. Issue #271 does
not prevent work on this development branch. A capability LexLean, PrismPM or
prism-stdlib cannot yet express is an upstream issue for those projects, never a reason for new
Python or shell. The logic already moved: the command surface, the register, the
converter (`rule30-api/src/Convert.lex.tex`), the engine's learning rule and schedule
(`Engine.lex.tex`), the relation and recurrence engines (`Discovery.lex.tex`), all with
certified rust-std roots.

The research execution modules are authored directly in LexLean:
`ResearchExecution` supervises one local tool through `LexLeanStd.Host`, and
`ResearchRunner` connects its lifecycle to `Research`. A process exit is not a
proof receipt. Report review must establish the exact contextual sequent,
kernel replay, axiom policy and snapshot before returning a checked answer.
`ResearchVerification` owns a fixed LexLean verification job and the ordered
command/attestation reads. Its accepted outcome is validated report data;
`ResearchProof` promotes it only after `CandidateBinding` recomputes the candidate
semantic identity and compares the audited declaration's actual type with the
requested contextual goal. `ResearchRunner.Event.reviewed` refuses checked
answers; submit proof jobs through `Event.proof`. The binding schema encodes the
inspected source type and closed target as core arenas in the sequent; source
inspection must establish their origin and snapshot before dispatch.
Maintenance reports have a separate result kind. Cancellation consumes the
outstanding host reply before issuing stop; failed cleanup retains ownership
and halts dispatch. Native application wiring, source inspection, strategy planner and
publication path still need completion; these modules do not replace the
legacy engine yet. Add every new application or library module and its modeled
features to `ResearchCatalog`, and add behavioral evidence for the capability;
a module-count theorem alone does not establish feature completeness.

## A round of the loop

Retired (2026-11-01): the research runs inside the repository, in the engine on GitHub Actions
(see "The engine"); sessions add features to the repository and do not run proposal rounds. What
follows describes the rounds that produced rounds 1 to 5 and is kept as history.

A proposal round is a saved workflow, `.claude/workflows/rule30-round.js`, run with the
lenses as arguments (`{round, lenses: [{key, prompt}], extra}`): one agent per lens proposes
the best exact theorem it yields (or the exact point where it stops), two skeptics per proposal
try to refute it (truth against the Lean definitions; routing against the refuted claims), and
the survivors and confident salvage are mechanized one at a time in new research modules, each
waiting for the gate and running one Lean process. Publishing (`theorem add`), the register
(`frontier add|set`, refuted routes included) and the commit stay with the orchestrator.

Induction feeds the round: `bin/r30 discover --window 256 --degree 2` runs the relation
engine (Gaussian elimination over F2) and the recurrence engine (Berlekamp-Massey) of
`rule30-api/src/Discovery.lex.tex` on the basis of `Sequences.lex.tex` (the paper's notions
evaluated from the host definitions; `bin/r30 sequences --write` refreshes it, one Lean run of
about six minutes), each output certified by a sound validator, and lists the relations the
register does not already imply (`new`), each with its κ-label and its window. A `new`
relation is a candidate statement for a lens, never a result: `--write` records the batch as
`observed` claims, `frontier check` keeps them true on their window, and one becomes `proved`
only through a Lean theorem (`theorem add`, then `frontier set --status proved --lean`). Read
the `consequence` class before proposing: a relation the engine derives from the register is
already a corollary. Do not widen the basis by enumerating cells or positions: add a notion
only as a lexeme of the paper.

`bin/r30 audit` classifies every conditional refutation of the period in the library (a theorem
concluding `¬ CenterPeriodic T P`, `Problem1` or `False` under a period) as dead (a hypothesis
refuted under a period by a named theorem), live-discharged (the composition closes in Lean: a
proof) or open with its open hypotheses (`--write` records them in `rule30-api/model/audit.toml`
and `Audit.lex.tex`, `claim <id> --related` lists them, `--cached` reads them without Lean).
The round opens with the Induce phase (`induce: false` skips it): one agent runs `bin/r30
discover --window 256 --degree 2 --json` and `bin/r30 audit --json`, and the observed relations
not in the register and the open audit obligations reach every lens as context and go straight
to Refute and Mechanize as proposals of their own.

## The engine

The loop above also runs by itself on GitHub Actions (`.github/workflows/engine.yml`,
rendered from `rule30-api/src/Engine.lex.tex` by `api sync`): every thirty minutes,
on dispatch and on pushes of the engine's inputs, `bin/r30 engine tick --commit --push`
builds the library (as the gate's `make core` does: `LexLeanRuntime.Laws`, which no Lake
root covers, then `lake build`; `modules.build` does the same for `module build` and
`deduce`), runs induction (`sequences --write` when its inputs changed,
`discover --write`), pruning (`audit --write`), deduction (`deduce`), learning and
hypotheses (the certified root `mint`), commits through the unchanged gate (`commit --wait`, in the foreground) and pushes
only when `origin/main` is still the tick's base. You intervene only by pushing
features; the engine's commits are yours to read like any other.

```
bin/r30 deduce [--budget-minutes N] [--claims <ids>] [--dry-run]   # prove the observed claims for all t
bin/r30 engine tick [--budget-minutes N] [--commit] [--push]        # one cycle (CI runs it with --commit --push)
bin/r30 engine status                                               # the last tick, the ledger, the weights
bin/r30 engine hypotheses [--budget N]                              # the tick's hypotheses stage alone
bin/r30 engine prune [--apply]                                      # the gate's evidence a next run can use; --apply deletes the rest
bin/r30 commit -m "..." --wait [--coauthor ""]                      # the gate in the foreground (the engine's path)
```

- **Deduction.** The portfolio (`enginemodel.PORTFOLIO`) is four deterministic
  templates under `tools/r30/templates/`, each pinned in `Engine.lex.tex` by the
  SHA-256 of the template and of its renderer `deduce.py`: `library-rewrite` (the
  columns into the diagonals, one rule step definitionally, the library's equalities
  from `mentions` and the register's proved relations, Boolean case analysis; a
  publishable library theorem that states the relation proves the claim with no new
  theorem, outcome `known`, checked before any strategy runs whatever the learned
  order), `step-induction` (the
  diagonals `rdiag 0..J`, `ldiag 0..D`, at `t` and `2t`, as a finite system whose
  orbit the kernel decides), `period-reduction` (the words of the right system
  read from the row register modulo `2^j`) and `counterexample`. The Boolean core
  of each is decided in Python first; Lean runs only when it holds. Accepted
  theorems go to `Rule30UOR.Deduced` (the engine's module: never edit it by hand);
  one whose statement κ a library theorem already has is taken out again and the
  library theorem proves the claim (outcome `known`: no statement is proved twice,
  `kappa --duplicates` prints no group), and the claim is set `proved` only with a
  published, kernel-checked theorem (`frontier check`).
- **Adding a strategy** means authoring its selection, applicability and candidate
  construction in LexLean. The Python portfolio and templates above describe the
  legacy executor, not an extension point. Preserve its identity discipline:
  changed strategy inputs get a new digest, and unchanged attempts are not repeated.
- **The ledger** `rule30-api/model/engine.toml` records every attempt (claim κ,
  strategy, template digest, family, outcome, failure point, seconds, and for
  `library-rewrite` the library digest: the research modules' sources and the
  register's proved relations); no (claim, strategy, digest, library) is attempted
  twice, so `library-rewrite` runs again once the library changed. An attempt the
  deduction deadline cuts is not recorded (it stays pending), and a success is
  recorded only once the register has it. The weights (plasticity) are a function
  of the attempts, decided in bounds by `Engine.lex.tex`.
- **Hypotheses.** The engine's role is to label new hypotheses. `rule30-api/src/Hypotheses.lex.tex`
  decides what is live and what is known; its root `mint` runs on the ledger's failed
  `library-rewrite` attempts (the exclusion each names) and the audit's open hypotheses, each read
  as its meaning: the canonical form of the Lean type closed over the variables it reads
  (`audit.lean.tmpl`, in the vocabulary of the gate's statement κ), labelled by the SHA-256 of that
  form. New rows go to `rule30-api/model/hypotheses.toml` (`r30/hypotheses/1`), at most the model's
  `hypothesisBudget` a tick; none is a claim of the register and none is promoted here. The store is
  no input of `mint` but as the labels to leave out, so minting ends when it holds what the ledger
  and the audit give; a tick that minted is not idle.
- **The certified roots** (`bin/r30 api production`, cached by the workflow under the digest of the
  sources) are the only runtime of `learnAll`, `schedule`, `mint` and the discovery engines: a root
  that cannot run ends the tick `error`. `engine status` prints the runtime each stage used.
- **Homeostasis.** The gate's share is reserved first and never cut (1.25 times its
  last measured duration when that is larger; the gate's own record cannot hold it, so
  the next tick measures it from the commit's time); every other stage may take its
  model share, deduction what the earlier stages left. An overrunning stage is cut
  (an attempt never runs past the deduction deadline), and a cut is not a
  measurement.
- **Idle.** A tick with nothing to do (nothing changed, nothing cut, nothing
  pending) commits nothing; the workflow marks the commit settled (also after a
  refused or failed tick, or a push the remote rejected while `main` had not moved)
  and later ticks on it stop after the checkout until a new commit reaches `main`. A
  tick a budget cut ends `cut` and settles nothing; a run whose commit is no longer
  `main`'s tip stops after the checkout (`stale` when main moved during the setup).
  Before caching, the workflow runs `engine prune --apply` (the current tools key,
  the newest LexLean attestation per project, never a certificate), and the job log
  carries the gate's log. Kill switch: repository variable `R30_ENGINE=off`. A tick
  run by hand leaves its record in the ledger; the next tick accepts that one dirty
  file.

## Publishing retained or generated host evidence

New proof candidates are authored in LexLean. The following commands publish
declarations already present in the retained or generated host library.

1. Confirm the declaration uses the paper's vocabulary: `twopow`, `bxor`,
   `rowBit`, `naturalBit` and named predicates. Use the module registration API
   for generated research modules; never hand-edit Lake roots or the audit.
2. `bin/r30 theorem add Rule30UOR.<Module>.<name>`. The entry lands in
   `r30.observation` (override with `--lexicon`), the statement at the end of
   `Observations.lex.tex` (override with `--target`). Known limitation: a
   hypothesis that is itself a quantified statement is refused by `lexlean
   check`; name the hypothesis as a predicate in Lean instead.
3. `bin/r30 verify paper --modules src/Observations.lex.tex`.
4. Record what it means: `bin/r30 frontier add|set`, and a paragraph in
   `rule30-lexlean/STRATEGY.md` if it changes the strategy. Negative results
   are recorded too; see the refuted claims in `frontier.toml`.
5. `bin/r30 commit -m "..." --push`. The gate refreshes the PDFs into the commit.

## What the paper can and cannot say

LexLean's specification (§4.2) rejects free expository paragraphs and
arbitrary natural language, so the LexLean documents carry no abstract,
introduction or discussion: every sentence in them is a checked statement or
a proof step. Their contextual layer is therefore built from what LexLean
does admit, all of it verified:

- **Defining equations.** `bin/r30 define` publishes, for each host definition,
  the equation lemma Lean derives from it (`<def>.eq_n`) as a `lemma` named
  `<notion>-definition` in the Notions section of `Observations.lex.tex`, so a
  reader learns what `centergate(Q, t)` is from the paper and the kernel
  confirms it. LexLean's own definition environments cannot be used for these
  notions: they generate their own Lean, and the theorems are about the host's.
- **Structure.** Sections with phrase headings (`r30.doc` label-words), the
  Frontier module (proved reductions and refuted routes as theorems), and the
  theorem/lemma/corollary distinction.
- **Names.** Component ids are read: `center-defect-coupling`,
  `periodic-black-no-arrival`.

Exposition that is not a checked statement (why a route was tried, what a
construction means, how the parts fit) belongs in `STRATEGY.md`, `frontier.toml`
notes, and the README, and is shipped beside the attested PDFs, never inside
them. Adding a prose environment to LexLean would be a change to LexLean's
guarantee ("no semantically untracked prose path"), which is a decision for
that project, not a workaround to take here.

## The register is the plan

`frontier.toml` is where the proof is planned and where it is not allowed to
drift. Every claim has a status and, when it is `proved`, a Lean name that
`frontier check` confirms is kernel-checked under `{propext, Quot.sound}` and
published as a lexeme; a `refuted` claim names its Lean refutation or the
experiment that refutes it; `depends` records which claims a claim rests on.
`make check-research` runs the check, so a commit cannot carry an unbacked
"proved". The register is also a LexLean document: `bin/r30 frontier render`
(run automatically by `frontier add` and `set`) writes
`rule30-paper/src/Frontier.lex.tex`, in which every proved or refuted claim
with a published theorem is restated as a theorem block generated from its
Lean type and closed by its lexeme, so `lexlean verify` checks the content of
the register and `frontier check` refuses a stale render. Work happens only on `open` claims; a new route is an `open` claim
before it is a theorem, and a dead route stays in the file as `refuted` so it is
not walked again. PrismPM models both the research register and the application:
open claims remain open, finite observations remain observations, and proof
status requires kernel evidence. The API imports the vendored prism-stdlib
`Foundation.Arch` and `Foundation.Qual` modules for stakeholders, concerns,
views and quality, and the locked LexLean standard library for executable
components. Its production roots compile to certified Rust libraries.
Tools may construct proof candidates; only verification establishes a result.
The research controller and runner track their contexts, dependencies, costs
and evidence so that execution remains directed at the open obligations.

## Layout

| Path | Role |
| --- | --- |
| `rule30-paper/src/*.lex.tex`, `rule30-paper/glossary/` | the paper and its lexicons (generated entries) |
| `rule30-lexlean/` | the LexLean core (`Core.lex.tex`) and `STRATEGY.md`, the research log |
| `rule30-core-lean/Rule30UOR/` | host Lean research modules; `Interfaces/PartNN.lean` are the parts of `Interfaces` |
| `rule30-core-lean/Rule30UOR/Constructive.lean`, `KitConstructive.lean` | choice-free helpers and choice-free proofs of the kit results used here |
| `Rule30PrizeKit/` | the Wolfram prize kit, unchanged |
| `rule30-bridge/` | the bridge from the paper's theorems to the kit's `Problem1` |
| `frontier.toml` | the claim register (`bin/r30 frontier`) |
| `tools/r30/` | the command surface and MCP server (deprecated Python runtime, being moved to LexLean) |
| `scripts/` | the validation gate, packaging and policy checks; tests in `scripts/tests/` |
| `experiments/` | finite diagnostics on the seed |

## Operating the gate

The gate (`bin/r30 commit`, the pre-commit and pre-push hooks running
`scripts/validate_git_tree.py`) is the one expensive step, and its failures of
the last day were all operational: the kernel replay needs about 41 GB of
virtual and 12 GB of resident memory on a 31 GB machine, and anything that
limits or competes with it looks like a proof failure. Run it from a plain
shell and leave the machine to it; iterate with the module-level commands and
commit once per batch.

- Launch `bin/r30 commit` from a plain shell: never under `ulimit -v`, a
  thread cap or a sandbox. The gate inherits them, and `leanchecker` then
  cannot map the toolchain.
- Run no agent workloads, `lake build` or `lexlean verify` while the gate runs.
  `bin/r30` and the hooks set `oom_score_adj=1000`, so under memory pressure
  the gate dies before the editor, and the rejection is then not about the proof.
- The gate reuses its evidence. Lake build directories, LexLean attestations
  (keyed by their exact inputs) and the kernel-replay receipts of
  `scripts/replay_research.py` (one per research module, κ-addressed: keyed
  by the module's κ-label, the SHA-256 of the canonical S-expression of the
  declarations the kernel replays as UOR-Foundation/uor-addr mints labels,
  plus the proof tools, never by the `.olean` bytes, the path or the Git
  state, so a comment, a docstring or a renamed binder replays nothing;
  `bin/r30 kappa <modules>` prints the labels) live under the Git common
  directory in `rule30-validation/` and survive rejections, so a retry replays
  only what changed. Outside the gate the receipts are in `.r30/replay`.
- Generated modules (`bin/r30 api sync`) chunk every literal list through
  `prim append` below `semantic.CHUNK` elements: the pinned notation's reader
  refuses deeper nesting (LLT4001). Do not build long lists by hand.
- Iterate with `bin/r30 check`, `bin/r30 verify ... --modules`, `bin/r30 module
  build` and `make check-tooling`; use the gate once per batch, and
  `bin/r30 gate` to watch it.

## What not to do

- Do not edit `lexlean.lock`, `pdf-manifest.json`, the PDFs or `verified-latest/`; the gate generates them.
- Do not add `Classical.*`, `Exists.choose`, `open Classical`, or `\allowaxioms{Classical.choice...}` anywhere; `scripts/check_no_choice.py` rejects them.
- Do not claim a result the kernel has not checked. `frontier.toml` has `open`, `proved`, `refuted`, `retired` and `observed` (a relation certified on a window by `bin/r30 discover`, pending deduction); a conjecture is `open` or `observed` until `bin/r30 axioms` passes on its Lean name.
- Do not bypass the hook (`ALLOW_NON_LEXLEAN_AUTHORING=1`) for proof content.
