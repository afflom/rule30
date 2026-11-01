Feature: engine

  The engine on GitHub Actions: the workload, the tick (induction, pruning, deduction, learning, the gate), the portfolio of proof templates, the learning layer and the ledger.

  @engine-workload @build
  Scenario: Engine.lex.tex declares the workload as data (the workflow, its triggers: a schedule at minutes 17 and 47, dispatch, and pushes of the engine's inputs to main; one concurrency group that never cancels a run; runs-on ubuntu-24.04; timeout 340 minutes; permissions contents and actions write; the one secret GITHUB_TOKEN; the actions it uses; the stages of a tick with their budgets; the cache families), and the kernel decides that no secret but GITHUB_TOKEN is read, that the permissions are exactly contents and actions with write, that the stage budgets fill the tick budget and with the setup fit the timeout, that the gate keeps its share, that the cron minutes are off the hour and thirty minutes apart, that there is one concurrency group, and that every action used is one the repository already used; api sync renders .github/workflows/engine.yml from that data (guarded by the repository and the kill switch R30_ENGINE) and api check refuses drift, a secret other than GITHUB_TOKEN, an action beyond those already used, or a pull_request trigger.
    Given .github/workflows/engine.yml
    When the suite exercises engine-workload
    Then its oracle accepts it: bin/r30 api check; bin/r30 verify api --modules src/Engine.lex.tex; scripts/tests/test_engine.py

  @engine-tick @build
  Scenario: bin/r30 engine tick [--budget-minutes N] [--commit] [--push] runs one deterministic cycle from a clean checkout: it records the base commit, builds the library, runs induction (sequences --write only when the evaluation program or the κ-labels of the modules it imports changed, discover --write at the committed window), pruning (audit --write), deduction (deduce within the remaining budget) and learning (learnAll over the tick's outcomes, api sync), splits the budget across the stages from their measured durations in the ledger (the gate's own duration measured by the next tick from the commit's time) with the gate's share reserved and never cut, ends idle without a commit when nothing changed (the workflow then marks the commit settled, as it does a refused or failed tick, and later runs on it stop after the checkout), commits in the foreground through the unchanged pre-commit gate (commit --wait) and pushes only when origin/main still is the base, dropping the work otherwise; never a force push.
    Given tools/r30/engine.py
    When the suite exercises engine-tick
    Then its oracle accepts it: scripts/tests/test_engine.py

  @engine-status @build
  Scenario: bin/r30 engine status prints the last tick (start, base, stages with seconds and allowances, counts, outcome), the network (units: the basis sequences; synapses: the observed, proved and refuted relations; events: the ticks), the attempts by outcome, the pending attempts and the learned weights; the workflow appends it to the job summary.
    Given tools/r30/engine.py
    When the suite exercises engine-status
    Then its oracle accepts it: scripts/tests/test_engine.py

  @deduce-command @build
  Scenario: bin/r30 deduce [--budget-minutes N] [--claims ids] [--dry-run] attempts every observed claim for all t with the portfolio in the learned order: each attempt renders one theorem from a template into a scratch file under .r30/deduce, checks it with one Lean process and accepts it only when its axioms are among propext and Quot.sound; accepted theorems are appended to Rule30UOR.Deduced and built; one whose statement κ a library theorem already has is removed again and the claim is proved by that library theorem (outcome known: no statement is proved twice, kappa --duplicates prints no group), the others are published (theorem add) and recorded (frontier set --status proved --lean); a relation the orbit of the diagonals breaks beyond its window is refuted by a decided counterexample.
    Given tools/r30/deduce.py
    When the suite exercises deduce-command
    Then its oracle accepts it: bin/r30 deduce; bin/r30 frontier check; scripts/tests/test_engine.py

  @strategy-portfolio @build
  Scenario: The portfolio is four deterministic Lean proof templates under tools/r30/templates, each pinned in Engine.lex.tex by the SHA-256 of its file and of the renderer that fills it (deduce.py): library-rewrite (the columns rewritten into the diagonals, one rule step unfolded, the library's equalities among the involved constants from mentions and the register's proved relations instantiated, closed by Boolean case analysis; a publishable library theorem that states the relation proves the claim with no new theorem, outcome known), step-induction (the diagonals the relation reads as a finite system stepped by the rule, the orbit decided by the kernel), period-reduction (the words of the right system read from the row register modulo their period 2^j) and counterexample; every applicable template's Boolean core is decided in Python first.
    Given tools/r30/templates
    When the suite exercises strategy-portfolio
    Then its oracle accepts it: bin/r30 api check; scripts/tests/test_engine.py

  @strategy-learning @build
  Scenario: Engine.lex.tex declares the learning layer: integer strategy weights per relation family, the bounded Hebbian rule learn (a success raises the weight by 2, a failure lowers it by 1, clamped to [1, 16]), learnAll and the scheduler schedule (applicable strategies by weight, ties by portfolio order) as production roots exported to certified Rust; the kernel decides that learn keeps every weight in bounds, that the committed weights are in bounds, that the schedule of every subset of the portfolio in every family is a permutation ordered by weight, and the fixtures the Python mirror computes; the tests compare the mirror with the certified roots.
    Given rule30-api/src/Engine.lex.tex
    When the suite exercises strategy-learning
    Then its oracle accepts it: bin/r30 verify api --modules src/Engine.lex.tex; scripts/tests/test_engine.py

  @engine-ledger @build
  Scenario: rule30-api/model/engine.toml (r30/engine/1) is the engine's ledger: the consolidated weights, every attempt (claim, κ-label, strategy, template digest, family, outcome proved, known, refuted, failed or timeout, failure point, seconds, theorem, tick) and the last ticks; no (claim κ, strategy, template digest) is attempted twice, and the weights are reproducible from the attempts.
    Given rule30-api/model/engine.toml
    When the suite exercises engine-ledger
    Then its oracle accepts it: scripts/tests/test_engine.py
