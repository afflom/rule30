Feature: register

  The claims of frontier.toml: the kernel is the judge of every proved one.

  @problem1 @open
  Scenario: The center column of Rule 30 from a single black cell is not eventually periodic.
    Given the register entry problem1 (Ruliology.CellularAutomata.Rule30Prize.Problem1)
    When the suite measures problem1
    Then the claim is reported open and never asserted

  @coupling-law @build
  Scenario: With the center agreeing at t, the next center defect is leftDefect(t,1) XOR ((not center t) AND rightDefect(t,1)); a center period is exactly this coupling at every later time.
    Given frontier.toml names Rule30UOR.WittDefect.center_periodic_of_coupling for coupling-law
    When the suite exercises coupling-law
    Then its oracle accepts it: frontier check: Rule30UOR.WittDefect.center_periodic_of_coupling kernel-checked under propext and Quot.sound and published

  @aperiodic-compensation @open
  Scenario: The bulk carries, with both edge bands stripped (interiorEightDiagonal: diagonals >= 3 on the regular side and >= 6 on the chaotic side), are never the ruler background trailingParity (t-2) XOR not timeParity t XOR trailingParity (t-4) XOR trailingParity ((t-4)/2) plus a periodic sequence: EightAperiodic. Equivalent to Problem 1 (left-band), to ThreeAperiodic (three-diagonal-band) and to InteriorAperiodic (interior-aperiodicity). This is the remaining obligation.
    Given the register entry aperiodic-compensation (Rule30UOR.LeftBand.EightAperiodic)
    When the suite measures aperiodic-compensation
    Then the claim is reported open and never asserted

  @q-adic-descent @some-true
  Scenario: The q-adic order of the observer defect carries a descent quantity.
    Given the register entry q-adic-descent and the refutation it names (Rule30UOR.WittDefect.observer_front_q_rank)
    When the suite reproduces q-adic-descent
    Then the route is reported refuted from its authority and nothing is established here

  @front-slack-descent @some-true
  Scenario: Phi_t = R_t - k_t (q-rank minus front depth) is a non-increasing potential.
    Given the register entry front-slack-descent and the refutation it names (experiment)
    When the suite reproduces front-slack-descent
    Then the route is reported refuted from its authority and nothing is established here

  @evaluation-point @some-true
  Scenario: Evaluating the observer polynomial at a constant point (0, 1, omega, omega^2) constrains the center.
    Given the register entry evaluation-point and the refutation it names (experiment)
    When the suite reproduces evaluation-point
    Then the route is reported refuted from its authority and nothing is established here

  @gate-phase-opposition @some-true
  Scenario: At a coupled arrival the gate phase is the negative of centerSign * rightPhase(start, 2).
    Given the register entry gate-phase-opposition and the refutation it names (Rule30UOR.WittDefect.head_import_path_rejects_negative_gate)
    When the suite reproduces gate-phase-opposition
    Then the route is reported refuted from its authority and nothing is established here

  @band-engines @some-true
  Scenario: The lhBandAgree / prefix-tail / late-scale engine hypothesis bundles refute a periodic center.
    Given the register entry band-engines and the refutation it names (Rule30UOR.Interfaces.lhBandAgree_engine_hypotheses_unsat)
    When the suite reproduces band-engines
    Then the route is reported refuted from its authority and nothing is established here

  @recurrent-central-collision @build
  Scenario: Problem 1 is equivalent to: under every hypothetical center period, central collisions do not occur arbitrarily late in the band of width 2P.
    Given frontier.toml names Rule30UOR.Frontier.problem1_iff_noRecurrentCentralCollision for recurrent-central-collision
    When the suite exercises recurrent-central-collision
    Then its oracle accepts it: frontier check: Rule30UOR.Frontier.problem1_iff_noRecurrentCentralCollision kernel-checked under propext and Quot.sound and published

  @saturation-reexcitation @some-true
  Scenario: Under a periodic center, each front arrival injects a unit boundary bit that re-excites the observer polynomial, so the center cannot settle (the RF/photonics heat-death reading).
    Given the register entry saturation-reexcitation and the refutation it names (Rule30UOR.WittDefect.periodic_arrival_no_crossing)
    When the suite reproduces saturation-reexcitation
    Then the route is reported refuted from its authority and nothing is established here

  @horizon-criterion @open
  Scenario: For every T and P > 0 there is an explicit horizon H(T, P) such that CenterPeriodic T P already fails on the window [T, T + H(T, P)]: a flip forced by the doubling zero diagonal of P reaches column -1 inside the window while the gated mirror forbids it there.
    Given the register entry horizon-criterion (experiment)
    When the suite measures horizon-criterion
    Then the claim is reported open and never asserted

  @horizon-certificate @build
  Scenario: For every transient T ≤ 512 and period 0 < P ≤ 128 the center disagrees with its lag-P shift at a time in [T, T + 32): the horizon H = 32 is a kernel-checked certificate on these ranges.
    Given frontier.toml names Rule30UOR.Horizon.horizon_thirty_two for horizon-certificate
    When the suite exercises horizon-certificate
    Then its oracle accepts it: frontier check: Rule30UOR.Horizon.horizon_thirty_two kernel-checked under propext and Quot.sound and published

  @left-defect-sourcing @build
  Scenario: Under a periodic center, a left defect at depth k at time t is sourced by a right column-one defect at a time in [t, t + k); equivalently column-one agreement on [t, t + k) forces the whole left cone of depth k at t to agree.
    Given frontier.toml names Rule30UOR.LeftCone.left_defect_sourced for left-defect-sourcing
    When the suite exercises left-defect-sourcing
    Then its oracle accepts it: frontier check: Rule30UOR.LeftCone.left_defect_sourced kernel-checked under propext and Quot.sound and published

  @first-failure-2adic @some-true
  Scenario: The first time a hypothetical center period (T, P) fails is governed by the 2-adic data of P and T (the scale mismatch between the periodically seeded right half and the doubling-time reconstruction of the left edge), so the closing invariant can be read off the first failing comparison.
    Given the register entry first-failure-2adic and the refutation it names (experiment)
    When the suite reproduces first-failure-2adic
    Then the route is reported refuted from its authority and nothing is established here

  @ledger-diagonal @build
  Scenario: The center column is the complement of the diagonal of the carry ledger: center t = not (bit t of winWitt 0 t), because row t = q^t XOR ledger and the central trinomial coefficient of q^t is odd; hence a center period is exactly a period of the ledger diagonal.
    Given frontier.toml names Rule30UOR.Ledger.centerPeriodic_iff_ledgerPeriodic for ledger-diagonal
    When the suite exercises ledger-diagonal
    Then its oracle accepts it: frontier check: Rule30UOR.Ledger.centerPeriodic_iff_ledgerPeriodic kernel-checked under propext and Quot.sound and published

  @periodic-finite-kernel @build
  Scenario: A periodic center has a finite 2-kernel: under CenterPeriodic T P every subsequence t -> center(2^k t + r), r < 2^k, is one of an explicit finite family (the kernel subsequences with 2^k < T + P, and t -> if t = 0 then b else center(T + (u t + v) mod P) with u, v < P).
    Given frontier.toml names Rule30UOR.Automatic.centerKernelFinite_of_centerPeriodic for periodic-finite-kernel
    When the suite exercises periodic-finite-kernel
    Then its oracle accepts it: frontier check: Rule30UOR.Automatic.centerKernelFinite_of_centerPeriodic kernel-checked under propext and Quot.sound and published

  @center-infinite-kernel @open
  Scenario: The center column is not 2-automatic: its 2-kernel, the family of subsequences t -> center(2^k t + r) with r < 2^k, is infinite. By Christol this is the transcendence of the series sum center(t) y^t over F_2(y); by Rowland-Yassawi it says the center is not a column of any linear cellular automaton over F_2.
    Given the register entry center-infinite-kernel (experiment)
    When the suite measures center-infinite-kernel
    Then the claim is reported open and never asserted

  @kernel-self-similarity @build
  Scenario: A finite 2-kernel forces a dyadic self-similarity of the center: some k < k' with center(2^k' t) = center(2^k t) for all t (pigeonhole along the zero path of the kernel tree); hence Problem 1 follows from NoDyadicSelfSimilarity.
    Given frontier.toml names Rule30UOR.Automatic.problem1_of_no_dyadic_self_similarity for kernel-self-similarity
    When the suite exercises kernel-self-similarity
    Then its oracle accepts it: frontier check: Rule30UOR.Automatic.problem1_of_no_dyadic_self_similarity kernel-checked under propext and Quot.sound and published

  @no-dyadic-self-similarity @open
  Scenario: For all k < k' there is a time t with center(2^k' t) != center(2^k t): the center column is not self-similar under any dyadic dilation.
    Given the register entry no-dyadic-self-similarity (Rule30UOR.Automatic.NoDyadicSelfSimilarity)
    When the suite measures no-dyadic-self-similarity
    Then the claim is reported open and never asserted

  @dilation-reduction @build
  Scenario: A finite 2-kernel makes every dilation sequence j -> center(2^j t) eventually periodic with one common period; hence Problem 1 follows if a single dilation sequence, in particular the dyadic column j -> center(2^j), is not eventually periodic.
    Given frontier.toml names Rule30UOR.Automatic.problem1_of_dyadic_column_aperiodic for dilation-reduction
    When the suite exercises dilation-reduction
    Then its oracle accepts it: frontier check: Rule30UOR.Automatic.problem1_of_dyadic_column_aperiodic kernel-checked under propext and Quot.sound and published

  @dyadic-column-aperiodic @open
  Scenario: The dyadic column j -> center(2^j) is not eventually periodic.
    Given the register entry dyadic-column-aperiodic (Rule30UOR.Automatic.DyadicColumnAperiodic)
    When the suite measures dyadic-column-aperiodic
    Then the claim is reported open and never asserted

  @base-generic-reduction @build
  Scenario: For every base b >= 2 and every t, Problem 1 follows if the b-dilation sequence j -> center(b^j t) is not eventually periodic: a periodic center has a finite b-kernel, a finite b-kernel forces a b-adic self-similarity, and that makes every b-dilation sequence eventually periodic.
    Given frontier.toml names Rule30UOR.Automatic.problem1_of_dilation_aperiodic_in_paper for base-generic-reduction
    When the suite exercises base-generic-reduction
    Then its oracle accepts it: frontier check: Rule30UOR.Automatic.problem1_of_dilation_aperiodic_in_paper kernel-checked under propext and Quot.sound and published

  @some-base-dilation-aperiodic @open
  Scenario: There are a base b >= 2 and a time t such that the dilation sequence j -> center(b^j t) is not eventually periodic.
    Given the register entry some-base-dilation-aperiodic (experiment)
    When the suite measures some-base-dilation-aperiodic
    Then the claim is reported open and never asserted

  @kappa-collapse @build
  Scenario: kappa-collapse at scale K (every cone window response at scales >= K vanishes, i.e. the carries no longer reach the center) is exactly a center period 2^K from time 0; the horizon certificate refutes it for K <= 7, and Problem 1 is equivalent to no kappa-collapse at any scale together with no period that is not a power of two.
    Given frontier.toml names Rule30UOR.Automatic.kappaCollapse_iff for kappa-collapse
    When the suite exercises kappa-collapse
    Then its oracle accepts it: frontier check: Rule30UOR.Automatic.kappaCollapse_iff kernel-checked under propext and Quot.sound and published

  @dyadic-response-reduction @build
  Scenario: At time 2^j the right cell at distance 2^j is the black edge, so center(2^(j+1)) = not center(2^j) XOR response(2^j, j); hence Problem 1 follows if the responses on the dyadic diagonal, j -> response(2^j, j), are not eventually periodic.
    Given frontier.toml names Rule30UOR.Automatic.problem1_of_dyadic_response_aperiodic for dyadic-response-reduction
    When the suite exercises dyadic-response-reduction
    Then its oracle accepts it: frontier check: Rule30UOR.Automatic.problem1_of_dyadic_response_aperiodic kernel-checked under propext and Quot.sound and published

  @dyadic-response-aperiodic @open
  Scenario: The responses on the dyadic diagonal, j -> response(2^j, j) (the window [2^j, 2^(j+1)) read at the center), are not eventually periodic.
    Given the register entry dyadic-response-aperiodic (Rule30UOR.Automatic.DyadicResponseAperiodic)
    When the suite measures dyadic-response-aperiodic
    Then the claim is reported open and never asserted

  @all-rules-facet @build
  Scenario: Every elementary rule has a unique algebraic normal form over F_2 (decided for all 256 codes), every normal form is its linear part XOR its nonlinear part, and Rule 30 is the unique code with normal form a XOR b XOR c XOR bc: the ledger decomposition is coherent across all rules, and the solution is a property of the single carry monomial bc under the linear part 1 + X + X^2.
    Given frontier.toml names Rule30UOR.Rules.rule_eq_linear_xor_carry for all-rules-facet
    When the suite exercises all-rules-facet
    Then its oracle accepts it: frontier check: Rule30UOR.Rules.rule_eq_linear_xor_carry kernel-checked under propext and Quot.sound and published

  @edge-interior-split @build
  Scenario: Two carry events of every row are explicit (the left edge pair and the right pair at the right edge); removing them splits the ledger by linearity into an edge-sourced ledger, the Rule-150 evolution of a periodic source, and the ledger of the interior carries, and center t = not (edgeDiagonal t XOR interiorDiagonal t).
    Given frontier.toml names Rule30UOR.EdgeSplit.center_eq_not_bxor_diagonals for edge-interior-split
    When the suite exercises edge-interior-split
    Then its oracle accepts it: frontier check: Rule30UOR.EdgeSplit.center_eq_not_bxor_diagonals kernel-checked under propext and Quot.sound and published

  @edge-diagonal-formula @build
  Scenario: The edge diagonal is an explicit 2-automatic expression: edgeLedger t is the Rule-150 propagation of the edge events, so edgeDiagonal t = edgeFormula t t, the XOR over m < t of trinomialParity (t-1-m) (t-2m-1) XOR [rdiag 1 m] trinomialParity (t-1-m) (t-2); hence center t = not (edgeFormula t t XOR interiorDiagonal t).
    Given frontier.toml names Rule30UOR.EdgeSplit.center_eq_not_formula_xor_interior for edge-diagonal-formula
    When the suite exercises edge-diagonal-formula
    Then its oracle accepts it: frontier check: Rule30UOR.EdgeSplit.center_eq_not_formula_xor_interior kernel-checked under propext and Quot.sound and published

  @interior-diagonal-formula @build
  Scenario: Bit t of q^n times y is the convolution of the bits of y with the trinomial row (testBit_phiLinearPow_conv), so the interior diagonal is the explicit XOR over the rows m < t of the convolution of row m's interior carries with trinomialParity (t-1-m), and center t = not (edgeFormula t t XOR interiorFormula t t): the center is fully explicit in the carries.
    Given frontier.toml names Rule30UOR.EdgeSplit.center_eq_not_formulas for interior-diagonal-formula
    When the suite exercises interior-diagonal-formula
    Then its oracle accepts it: frontier check: Rule30UOR.EdgeSplit.center_eq_not_formulas kernel-checked under propext and Quot.sound and published

  @route-a-band-discharge @some-true
  Scenario: Route A (dyadic reflection): discharge the single-row spatial-agreement hypothesis of the terminal refutations 9.1496-9.1516 under a periodic center with Q = c 2^K P and K large, so that lhBandAgree(z+p+1, Q, 1, S) with S >= p + 3Q follows and the terminal theorems close Problem 1.
    Given the register entry route-a-band-discharge and the refutation it names (Rule30UOR.Interfaces.lhBandAgree_engine_hypotheses_unsat)
    When the suite reproduces route-a-band-discharge
    Then the route is reported refuted from its authority and nothing is established here

  @route-c-rank-drop @some-true
  Scenario: Route C (cyclotomic rank drop): link the carry-ledger congruences modulo q^(2^a) and the page charge to show the observer source flux cannot supply the q-divisibility needed to keep the q-rank non-negative as t grows, closing Problem 1.
    Given the register entry route-c-rank-drop and the refutation it names (Rule30UOR.WittDefect.observer_front_q_rank)
    When the suite reproduces route-c-rank-drop
    Then the route is reported refuted from its authority and nothing is established here

  @route-b-reset-mismatch @some-true
  Scenario: Route B (reset flux jump): between the doubling diagonal z+1 at time t and the reset diagonal z+3 at time t+1, which share the arrival time 2t-z-2 and hence the same import balance, the sum diagonalPhase + diagonalFlux changes by a unit, contradicting periodic_diagonal_import_balance and closing Problem 1.
    Given the register entry route-b-reset-mismatch and the refutation it names (Rule30UOR.Routes.diagonal_reset_sum_invariant)
    When the suite reproduces route-b-reset-mismatch
    Then the route is reported refuted from its authority and nothing is established here

  @edge-parity @build
  Scenario: The edge background of the center is the time parity: edgeDiagonal t = timeParity t, i.e. t mod 2. The column parity of the trinomial triangle is Thue-Morse shifted by one (columnParity (2e+1) = columnParity e, columnParity (2e+2) = not columnParity e, from trinomialParity n n = true), the right-pair part is the same sequence read at (t-2)/2 (sameParityColumn_eq), and the two cancel to the parity. Hence center t = not (timeParity t XOR interiorDiagonal t).
    Given frontier.toml names Rule30UOR.EdgeParity.edgeDiagonal_eq_timeParity for edge-parity
    When the suite exercises edge-parity
    Then its oracle accepts it: frontier check: Rule30UOR.EdgeParity.edgeDiagonal_eq_timeParity kernel-checked under propext and Quot.sound and published

  @interior-aperiodicity @build
  Scenario: Problem 1 is equivalent to the interior diagonal not being eventually periodic: CenterPeriodic T P gives InteriorPeriodic T (2P) and InteriorPeriodic T P gives CenterPeriodic T (2P), so Problem1 iff InteriorAperiodic.
    Given frontier.toml names Rule30UOR.EdgeParity.problem1_iff_interiorAperiodic for interior-aperiodicity
    When the suite exercises interior-aperiodicity
    Then its oracle accepts it: frontier check: Rule30UOR.EdgeParity.problem1_iff_interiorAperiodic kernel-checked under propext and Quot.sound and published

  @interior-kernel-reduction @build
  Scenario: The center is 2-automatic exactly when the interior diagonal is: a finite 2-kernel is closed under negation and under XOR with the time parity, so CenterInfiniteKernel iff not InteriorKernelFinite, and Problem 1 follows if the interior diagonal is not 2-automatic.
    Given frontier.toml names Rule30UOR.KernelParity.centerInfiniteKernel_iff_interior for interior-kernel-reduction
    When the suite exercises interior-kernel-reduction
    Then its oracle accepts it: frontier check: Rule30UOR.KernelParity.centerInfiniteKernel_iff_interior kernel-checked under propext and Quot.sound and published

  @characteristic-one-facet @build
  Scenario: The carry is the intersection of a row with its own translate (the characteristic-1 content of rule 30, the idempotent OR, against the characteristic-2 linear part whose Frobenius is the gasket). On the linear rows the self-intersection is exact: carry (q^(2m)) = 0 and carry (q^(2m+1)) is the run boundary of q^m; the linear self-carry lives on odd rows only.
    Given frontier.toml names Rule30UOR.Intersection.linear_self_intersection_even for characteristic-one-facet
    When the suite exercises characteristic-one-facet
    Then its oracle accepts it: frontier check: Rule30UOR.Intersection.linear_self_intersection_even kernel-checked under propext and Quot.sound and published

  @three-diagonal-band @build
  Scenario: The three inner diagonals of the regular side (carry bits 2t, 1, 2 of every row) contribute exactly the period-doubling sequence: center t = trailingParity (t-2) XOR interiorThreeDiagonal t for t >= 2, where interiorThreeDiagonal is the gasket parity of the carries on diagonals >= 3. Hence CenterPeriodic T P iff ThreeAgainstTrailing T P (T >= 2) and Problem 1 iff ThreeAperiodic: the deep interior can never be the period-doubling sequence plus a periodic sequence.
    Given frontier.toml names Rule30UOR.Band.center_eq_trailingParity_bxor_three for three-diagonal-band
    When the suite exercises three-diagonal-band
    Then its oracle accepts it: frontier check: Rule30UOR.Band.center_eq_trailingParity_bxor_three kernel-checked under propext and Quot.sound and published

  @stable-kernel @build
  Scenario: The trinomial kernel is dyadically stable: trinomialParity (2^(j+1)-1-m) d = trinomialParity (2^j-1-m) d for m, d < 2^j, so the dyadic column reads the carries of row m through the fixed kernel stableKernel m (the inverse 1/q^(m+1); row 2^j-1 is 1/q = 110110... below degree 2^j): center (2^j) = not stableFormula j for j >= 1, and DyadicColumnAperiodic iff StableFormulaAperiodic.
    Given frontier.toml names Rule30UOR.StableKernel.dyadicColumnAperiodic_iff_stable for stable-kernel
    When the suite exercises stable-kernel
    Then its oracle accepts it: frontier check: Rule30UOR.StableKernel.dyadicColumnAperiodic_iff_stable kernel-checked under propext and Quot.sound and published

  @dyadic-renormalization @build
  Scenario: The obligation renormalizes: the ruler trailingParity moves across 2^k P only on the class n = -1 mod 2^k, where it is the ruler one scale up twisted by [k odd]. Under a center period P the deep interior is exactly 2^k P-periodic off the class t = 1 mod 2^k, and on the class the sampled sequence u -> interiorThreeDiagonal (2^k u + 1) satisfies the same equation against the ruler with the same period P, for every k.
    Given frontier.toml names Rule30UOR.Band.threeClass_of_centerPeriodic for dyadic-renormalization
    When the suite exercises dyadic-renormalization
    Then its oracle accepts it: frontier check: Rule30UOR.Band.threeClass_of_centerPeriodic kernel-checked under propext and Quot.sound and published

  @scale-free-rows @build
  Scenario: Each row's contribution to the dyadic column is the same at every scale above the row (rowTerm (2^(j+1)) m = rowTerm (2^j) m for m < 2^j), so the dyadic column is the prefix parity of one fixed sequence dyadicRow and the block response is its block parity: center (2^(j+1)) = center (2^j) XOR blockParity j, wittRespBool (2^j) j = blockParity j. Problem 1 follows if the block parities of dyadicRow are not eventually periodic in j.
    Given frontier.toml names Rule30UOR.DyadicRow.center_twopow_succ_eq for scale-free-rows
    When the suite exercises scale-free-rows
    Then its oracle accepts it: frontier check: Rule30UOR.DyadicRow.center_twopow_succ_eq kernel-checked under propext and Quot.sound and published

  @left-band @build
  Scenario: The chaotic-side edge is regular for a few cells (ldiag 2 = 0, ldiag 3 = timeParity, ldiag 4 = 1, ldiag 5 = ldiag 6 = timeParity, ldiag 7 = 0), so the carries on the left diagonals 3..5 are [m odd] for m >= 5 (plus one event at row 3) and contribute not timeParity t XOR trailingParity (t-4) XOR trailingParity ((t-4)/2): for t >= 6, center t = rulerBackground t XOR interiorEightDiagonal t, with both edge bands stripped, and Problem 1 iff EightAperiodic.
    Given frontier.toml names Rule30UOR.LeftBand.center_eq_rulerBackground_bxor_eight for left-band
    When the suite exercises left-band
    Then its oracle accepts it: frontier check: Rule30UOR.LeftBand.center_eq_rulerBackground_bxor_eight kernel-checked under propext and Quot.sound and published

  @kernel-law @build
  Scenario: The freezing law of the linear transport: for a row m < 2^k and a time 2^k u + r (r < 2^k, u >= 1), rowTerm (2^k u + r) m = frozen k r m XOR trailingParity (u-1) AND second k r m, with frozen and second read off the row's contributions at u = 1 and u = 2. Hence every 2-kernel sequence of the center is explicit up to the rows at or above the scale: center (2^k u + r) = not (timeParity r XOR frozenPrefix k r XOR trailingParity (u-1) AND secondPrefix k r XOR lateTail k r u); the fixed dyadic row, the class renormalization and the band rulers are its instances, and a block of rows [2^j, 2^(j+1)) influences every later time only through its influence on the next two block-spans, modulated by the ruler.
    Given frontier.toml names Rule30UOR.KernelLaw.rowTerm_kernel_law for kernel-law
    When the suite exercises kernel-law
    Then its oracle accepts it: frontier check: Rule30UOR.KernelLaw.rowTerm_kernel_law kernel-checked under propext and Quot.sound and published
