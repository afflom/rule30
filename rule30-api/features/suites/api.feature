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
  Scenario: The production roots of Api.lex.tex (commands, commandCount) and of Rule30Core.lex.tex (rows, center, rdiag, towerWord, rulerBackground, centersFrom, rulerFrom) export to certified Rust packages through lexlean production build, kernel-checked under their stated axioms, and the published bundle replays with verify-artifact.
    Given rule30-api/production/request.json
    When the suite exercises rust-emission
    Then its oracle accepts it: bin/r30 api production; scripts/tests/test_r30.py

  @verified-core @build
  Scenario: Rule30Core.lex.tex declares the automaton's computational core (the rule on three cells, the row step, the rows, the center, the right diagonals rdiag, the tower of words towerWord, trailingParity, timeParity and the ruler background) as executable definitions whose production roots export to Rust; the kernel decides the first 32 centers and ruler values, rdiag 1 as the time parity on 64 times, center t = towerWord t t, the periods 2^j of the first words and the half periods 2^(j-1) of the first diagonals, the tower recursion on the first words and the agreement of the row cells with the right-edge recursion of Core.lex.tex; core-vectors.json (256 centers, 12 tower words, the ruler background below 512) is generated from the same model, cross-checked against the decided literals and identities, and published by the view. The pinned compiler has no Wasm or browser target, so the page reads the vectors rather than running the module.
    Given rule30-api/src/Rule30Core.lex.tex
    When the suite exercises verified-core
    Then its oracle accepts it: lexlean verify rule30-api (scripts/verify_lexlean.sh); bin/r30 api check; scripts/tests/test_r30.py

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

  @design-system @build
  Scenario: Presentation.lex.tex declares the design system of the site as data (colour tokens with their sRGB values in both themes, the contrast pairs the stylesheet uses, the type and spacing scales, the motion durations with their reduced-motion variant, the landing) and the kernel decides, in integer arithmetic over relative luminance, that every pair meets WCAG 2.2 AA (4.5:1 for text, 3:1 for controls and graphics) in both themes, that the scales increase, that targets are at least 24px and that reduced motion is instant; api sync writes the tokens into the site as CSS custom properties and api check refuses drift.
    Given rule30-api/src/Presentation.lex.tex
    When the suite exercises design-system
    Then its oracle accepts it: lexlean verify rule30-api (scripts/verify_lexlean.sh); bin/r30 api check; scripts/tests/test_r30.py DesignTests

  @standards-register @build
  Scenario: Standards.lex.tex names every external standard the implementation realizes (architecture, quality, accessibility, markup, graphics, metadata, provenance, schemas, API description, citation, licensing, canonical forms, attestations, the toolchains) with its authority, version, scope, realizers and check; the kernel decides that the ids are distinct, every standard has an authority and a realizer, every realizer is declared, every panel, artifact, journey, command, navigation and visualization id names a standard, and the toolchain rows carry the pinned versions; view render writes the artifacts the standards call for (openapi.json, sitemap.xml, provenance.jsonld, schema.json, attestations.intoto.json, standards.json, CITATION.cff).
    Given rule30-api/src/Standards.lex.tex
    When the suite exercises standards-register
    Then its oracle accepts it: lexlean verify rule30-api (scripts/verify_lexlean.sh); bin/r30 api check; scripts/tests/test_r30.py
