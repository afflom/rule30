Feature: discovery

  Induction mechanized: the basis of the map, the relation and recurrence engines, their certified roots, bin/r30 discover and the observed status.

  @discovery-basis @build
  Scenario: Sequences.lex.tex declares the basis of the map: 79 sequences of the paper's notions (the constant, the time and trailing parities, the ruler background, the center, the cells at positions -8..8, the right and left diagonals and the tower words j <= 12, the exposed masks k <= 8, the masked column, the two cones and the seven ledger diagonals), each with its lexeme, Lean constant, parameters and κ-label (sequence <lexeme> <parameters>), and its window for t < 512 evaluated from the host Lean definitions by bin/r30 sequences --write in one Lean file that proves every evaluation form equal to its host constant; the kernel decides that the ids and the κ-labels are distinct and that every window has 16 words below 2^32, and api check refuses data that is not the basis or whose labels are not the labels of its entries. dyadicRow, blockParity and wittRespBool are excluded, with the reason recorded.
    Given rule30-api/src/Sequences.lex.tex
    When the suite exercises discovery-basis
    Then its oracle accepts it: bin/r30 sequences --write; bin/r30 api check; lexlean verify rule30-api; scripts/tests/test_r30.py DiscoveryTests

  @relation-search @build
  Scenario: Discovery.lex.tex declares the contract RelationSearch (input a window of chunked Nat bit-vectors, output masks over the sequences; precondition IsWindow, postcondition AllRelationsHold, each with an executable validator and a soundness theorem), the realization RelationEngine (Gaussian elimination over F2 with a mask per pivot), the model RelationSearchModel, the transforms of the extended basis (shift, even and odd dilations, AND) as data, and the kernel decides on 64 times of the real data that the engine finds the edge parity, the left light cone, the cone identity cone-zero = cell(-1) and the increment law in the basis, and that its output passes the postcondition.
    Given rule30-api/src/Discovery.lex.tex
    When the suite exercises relation-search
    Then its oracle accepts it: lexlean verify rule30-api; bin/r30 api check; scripts/tests/test_r30.py DiscoveryTests

  @recurrence-search @build
  Scenario: Discovery.lex.tex declares the contract RecurrenceSearch (input one window as bits, output a connection polynomial with leading 1; precondition IsSequenceWindow, postcondition SatisfiesRecurrence: the recurrence holds for every L <= t < N), the realization RecurrenceEngine (Berlekamp-Massey over F2) and the model RecurrenceSearchModel; the certificate is the recurrence on the window, not its minimality; the kernel decides s(t) = s(t-2) for the time parity and the tower word 2 and s(t) = s(t-3) for the period-3 word 100.
    Given rule30-api/src/Discovery.lex.tex
    When the suite exercises recurrence-search
    Then its oracle accepts it: lexlean verify rule30-api; bin/r30 api check; scripts/tests/test_r30.py DiscoveryTests

  @discovery-roots @build
  Scenario: The production roots buildColumns, findRelations and findRecurrence of Discovery.lex.tex are executable, admit the allocation, overflow and recursion effects on rust-std, and apply their models through checked_apply with both the precondition and the postcondition checked at run time, so every output is accepted by a validator the kernel proved sound; they are requested beside the roots of Api and Rule30Core in production/request.json and runtime-roots.toml.
    Given rule30-api/production/request.json
    When the suite exercises discovery-roots
    Then its oracle accepts it: bin/r30 api production; bin/r30 api check; scripts/tests/test_r30.py DiscoveryTests

  @discover-command @build
  Scenario: bin/r30 discover [--window W] [--degree 1|2] [--write] runs the engines on the basis (the certified Rust of the roots, and is refused when they cannot run), reports every relation with its columns, κ-label (relation <sorted column labels>), class (register, trivial, consequence, new) and certificate (the rank before its dependent column), and the recurrence of every base window; --write appends the new relations to the register as status observed.
    Given tools/r30/discover.py
    When the suite exercises discover-command
    Then its oracle accepts it: scripts/tests/test_r30.py DiscoveryTests; bin/r30 discover --window 256 --degree 2

  @observed-status @build
  Scenario: The register has the status observed: a relation certified on a window (relation, window, κ-label), re-validated by frontier check against the committed windows and refused when it does not vanish; Register.lex.tex carries every claim's relation and κ-label and decides that every observed claim has both; Discovery.lex.tex decides that every relation of the register vanishes on its window; the Observer counts an observed claim as neither a real quality nor withdrawn, and the site renders its mark.
    Given frontier.toml
    When the suite exercises observed-status
    Then its oracle accepts it: bin/r30 frontier check; scripts/tests/test_r30.py DiscoveryTests

  @discovery-candidates @open
  Scenario: The relations and recurrences bin/r30 discover --window 256 --degree 2 finds on the committed basis beyond the register are candidates for deduction: measured on the window and reported, never asserted.
    Given the register entry discovery-candidates (tools/r30/discover.py)
    When the suite measures discovery-candidates
    Then the claim is reported open and never asserted
