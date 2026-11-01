Feature: api

  The LexLean API modules, the PrismPM model and the stakeholder view.

  @api-modules @build
  Scenario: The command surface, the register, the architecture and the presentation are LexLean semantic modules on prism-stdlib, verified by the gate.
    Given rule30-api/src
    When the suite exercises api-modules
    Then its oracle accepts it: lexlean verify rule30-api (scripts/verify_lexlean.sh); bin/r30 api check

  @prism-model @build
  Scenario: The model registers (authorities, ids, ledger, commands, standards, projection, contracts, errors, dependencies, runtime-roots, stdlib-package), the result schemas, the Gherkin suites and CONFORMANCE.md are generated from the register, the parser, the error table and the architecture, and drift is refused.
    Given rule30-api/model
    When the suite exercises prism-model
    Then its oracle accepts it: bin/r30 api check; scripts/tests/test_r30.py

  @rust-emission @build
  Scenario: The production roots of Api.lex.tex (commands, commandCount) export to certified Rust packages through lexlean production build, kernel-checked under its stated axioms, and the published bundle replays with verify-artifact.
    Given rule30-api/production/request.json
    When the suite exercises rust-emission
    Then its oracle accepts it: bin/r30 api production; scripts/tests/test_r30.py

  @observer @build
  Scenario: Observer.lex.tex records the object quadruple of every stakeholder vantage (the proof as the real object, the journey as the sensual object, the proved claims its panels render as real qualities, the panels as sensual qualities, the open claims as withdrawn) and the kernel decides withdrawal, nonempty overlap, symmetric interaction and gauge covariance over the register and the presentation.
    Given rule30-api/src/Observer.lex.tex
    When the suite exercises observer
    Then its oracle accepts it: lexlean verify rule30-api (scripts/verify_lexlean.sh); bin/r30 api check

  @current-view @build
  Scenario: The view workflow renders the artifacts Presentation.lex.tex declares, with the site, on every push to main, deploys them to GitHub Pages at the URL Application.lex.tex names, and runs no validation; the site opens on a choice of vantage and shows one step at a time, every step a rendered panel toward a goal on declared evidence, the journeys covering the Observer's poles in order and ending in verification as the kernel decides, and the page meets WCAG AA contrast with keyboard focus and reduced motion honoured.
    Given .github/workflows/view.yml
    When the suite exercises current-view
    Then its oracle accepts it: bin/r30 view render; scripts/tests/test_r30.py
