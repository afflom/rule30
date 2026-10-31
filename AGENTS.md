# Working in this repository

This file is for anyone, human or agent, who changes the proof surfaces. It is
short on purpose: the commands below return compact reports, so a session can
act on them without reading build logs.

## The one rule

LexLean is the authoring surface. Host Lean (`rule30-core-lean/Rule30UOR`) is
where proofs are written, but a theorem exists for the paper only once it has a
glossary entry and a statement in a `.lex.tex` file, verified by `lexlean`.
Never write a glossary entry by hand: generate it from the Lean declaration
with `bin/r30 theorem add`, which also writes the statement, checks it, and
elaborates the same probe `lexlean verify` will run. The generator refuses
what LexLean cannot state and says why (implicit binders, casts, `Bool.xor`
instead of `bxor`, `2 ^ k` instead of `twopow k`, a lexeme not visible from the
target lexicon). Fix the Lean statement, not the entry.

Every theorem depends on at most `propext` and `Quot.sound`. `Classical.choice`
is forbidden: `by_cases` on an undecidable proposition is a compile error, and
`cfomega` is `omega` without classical preprocessing (`Rule30UOR.Constructive`).

## The loop

```
bin/r30 status                         # HEAD, dirty files, frontier counts
bin/r30 frontier list                  # what is open, proved, refuted
bin/r30 lexicon search <text>          # find lexemes by id, surface, or Lean name
bin/r30 sig <Lean names>               # a declaration's type as an s-expression
bin/r30 unpublished <module prefixes>  # theorems without a lexeme, and whether they can be published
bin/r30 theorem preview <Lean names>   # the entry and statement, without writing
bin/r30 theorem add <Lean names>       # write entry + statement, lock, check the module, probe
bin/r30 check paper --modules src/Observations.lex.tex   # seconds
bin/r30 verify paper --modules src/Observations.lex.tex  # seconds; the real probe
bin/r30 axioms <Lean names>            # must print only propext, Quot.sound
bin/r30 frontier check                 # the register against the kernel (also run by the gate)
bin/r30 choice-audit                   # theorems depending on Classical.choice (must be none)
bin/r30 commit -m "..." [--push]       # commit through the pre-commit gate, in the background
bin/r30 gate                           # is that gate still running; its last stage and log tail
bin/r30 experiment run <name> [args]   # a finite diagnostic on the seed
```

Costs: `check`/`verify` of one module take seconds; `verify` of the whole paper
takes about six minutes (`Paper.lex.tex` is 13k lines); the pre-commit gate
takes twenty to thirty minutes and runs everything (tooling tests, Lean
build, vacuity and axiom audits, kernel replay, bridge, both LexLean projects,
PDFs). Use the module forms while iterating and the gate once per batch.

`--json` on any command gives the same report as JSON. The same commands are
available as MCP tools: `claude mcp add r30 -- python3 <repo>/tools/r30/mcp_server.py`.

## A theorem's life

1. State and prove it in a research module (`rule30-core-lean/Rule30UOR/*.lean`).
   Use the paper's vocabulary in the statement: `twopow`, `bxor`, `rowBit`,
   `naturalBit`, named predicates rather than inline quantifiers. `lake build
   Rule30UOR.<Module>` from `rule30-core-lean`.
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

## The register is the plan

`frontier.toml` is where the proof is planned and where it is not allowed to
drift. Every claim has a status and, when it is `proved`, a Lean name that
`frontier check` confirms is kernel-checked under `{propext, Quot.sound}` and
published as a lexeme; a `refuted` claim names its Lean refutation or the
experiment that refutes it; `depends` records which claims a claim rests on.
`make check-research` runs the check, so a commit cannot carry an unbacked
"proved". Work happens only on `open` claims; a new route is an `open` claim
before it is a theorem, and a dead route stays in the file as `refuted` so it is
not walked again. This is the one idea taken from PrismPM's model registers
(every registered capability covered by a fixture): every registered claim is
covered by kernel evidence. PrismPM itself compiles LexLean application models
into Cargo, Wasm and Hologram artifacts behind a Rust and devcontainer
toolchain; nothing in a proof repository needs those artifacts, so it is not a
dependency here.

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
| `tools/r30/` | the command surface and MCP server; `tools/split_interfaces.py` |
| `scripts/` | the validation gate, packaging and policy checks; tests in `scripts/tests/` |
| `experiments/` | finite diagnostics on the seed |

## What not to do

- Do not edit `lexlean.lock`, `pdf-manifest.json`, the PDFs or `verified-latest/`; the gate generates them.
- Do not add `Classical.*`, `Exists.choose`, `open Classical`, or `\allowaxioms{Classical.choice...}` anywhere; `scripts/check_no_choice.py` rejects them.
- Do not claim a result the kernel has not checked. `frontier.toml` has `open`, `proved`, `refuted` and `retired`; a conjecture is `open` until `bin/r30 axioms` passes on its Lean name.
- Do not bypass the hook (`ALLOW_NON_LEXLEAN_AUTHORING=1`) for proof content.
