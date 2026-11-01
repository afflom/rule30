# Interface: dyadic-response-aperiodic [open]

The responses on the dyadic diagonal, j -> response(2^j, j) (the window [2^j, 2^(j+1)) read at the center), are not eventually periodic.

Lean: `Rule30UOR.Automatic.DyadicResponseAperiodic`

## Chain from the root

- [?] problem1 — `Ruliology.CellularAutomata.Rule30Prize.Problem1`
- [✓] periodic-finite-kernel — `Rule30UOR.Automatic.centerKernelFinite_of_centerPeriodic`
- [✓] kernel-self-similarity — `Rule30UOR.Automatic.problem1_of_no_dyadic_self_similarity`
- [✓] dilation-reduction — `Rule30UOR.Automatic.problem1_of_dyadic_column_aperiodic`
- [✓] ledger-diagonal — `Rule30UOR.Ledger.centerPeriodic_iff_ledgerPeriodic`
- [✓] recurrent-central-collision — `Rule30UOR.CentralCollision.problem1_iff_no_recurrent_central_collision`
- [✓] coupling-law — `Rule30UOR.WittDefect.center_periodic_of_coupling`
- [?] aperiodic-compensation — `Rule30UOR.LeftBand.EightAperiodic`
- [✓] horizon-certificate — `Rule30UOR.Horizon.horizon_thirty_two`
- [✓] kappa-collapse — `Rule30UOR.Automatic.kappaCollapse_iff`
- [✓] dyadic-response-reduction — `Rule30UOR.Automatic.problem1_of_dyadic_response_aperiodic`
- [?] dyadic-response-aperiodic — `Rule30UOR.Automatic.DyadicResponseAperiodic`

## Notions (labels)

- `Rule30UOR.Automatic.DyadicResponsePeriodic` — lexeme `r30.observation::dyadic-response-periodic`
- `Rule30UOR.Core.twopow` — lexeme `r30.scale::twopow`
- `Rule30UOR.Scale.response` — lexeme `r30.scale::response`

## Exact facts about each notion

### `Rule30UOR.Automatic.DyadicResponsePeriodic` (3)
- `Rule30UOR.Automatic.dilationPeriodic_of_dyadicResponsePeriodic`
- `Rule30UOR.Automatic.dyadicResponsePeriodic_of_dilationPeriodic`
- `Rule30UOR.Automatic.responseParity_shift`

### `Rule30UOR.Core.twopow` (1887)
- `Rule30UOR.Antidiagonal.coneTerm_add_twopow_mul`
- `Rule30UOR.Antidiagonal.exposed_periodic`
- `Rule30UOR.Antidiagonal.orWord_half_periodic`
- `Rule30UOR.Antidiagonal.orWord_periodic`
- `Rule30UOR.Antidiagonal.pascalParity_add_twopow_mul`
- `Rule30UOR.Antidiagonal.rdiag_add_twopow_mul`
- `Rule30UOR.Antidiagonal.rdiag_period_half`
- `Rule30UOR.Antidiagonal.towerWord_add_half_mul`
- `Rule30UOR.Antidiagonal.towerWord_add_twopow`
- `Rule30UOR.Antidiagonal.towerWord_add_twopow_half`
- `Rule30UOR.Antidiagonal.towerWord_eq_row`
- `Rule30UOR.Antidiagonal.towerWord_half_period`
- `Rule30UOR.Antidiagonal.towerWord_mod`
- `Rule30UOR.Antidiagonal.towerWord_mod_half`
- `Rule30UOR.Antidiagonal.towerWord_period_doubles`
- `Rule30UOR.Antidiagonal.towerWord_period_halves`
- `Rule30UOR.Antidiagonal.wordWeight_eq_row`
- `Rule30UOR.Automatic.centerPeriodic_of_kappaCollapse`
- `Rule30UOR.Automatic.center_mod_of_kappaCollapse`
- `Rule30UOR.Automatic.center_twopow_succ`
- `Rule30UOR.Automatic.dyadic_column_step`
- `Rule30UOR.Automatic.dyadic_self_similar_of_kernel2Finite`
- `Rule30UOR.Automatic.kappaCollapse_iff`
- `Rule30UOR.Automatic.kappaCollapse_of_centerPeriodic`
- `Rule30UOR.Automatic.kernelSeq_odd`
- `Rule30UOR.Automatic.kernelSeq_step`
- `Rule30UOR.Automatic.kernelSeq_step_late`
- `Rule30UOR.Automatic.response_cone`
- `Rule30UOR.Automatic.twopow_add`
- `Rule30UOR.Automatic.twopow_dvd_of_le`
- `Rule30UOR.Automatic.twopow_ge_succ`
- `Rule30UOR.Automatic.twopow_mono`
- `Rule30UOR.Automatic.unflipped_succ`
- `Rule30UOR.Band.centerPeriodic_twopow_mul`
- `Rule30UOR.Band.dyadic_one_obligation`
- `Rule30UOR.Band.trailingParity_add_twopow_mul`
- `Rule30UOR.Band.trailingParity_twopow_add`
- `Rule30UOR.Band.trailingParity_twopow_mul_sub_one`
- `Rule30UOR.Band.trailingParity_twopow_sub_one`
- `Rule30UOR.ClassObligation.center_class_eq`
- `Rule30UOR.ClassObligation.eightClass_of_centerPeriodic`
- `Rule30UOR.ClassObligation.eightOffClass_of_centerPeriodic`
- `Rule30UOR.ClassObligation.eight_le_twopow_add_three`
- `Rule30UOR.ClassObligation.four_le_twopow_add_two`
- `Rule30UOR.ClassObligation.half_ge_four`
- `Rule30UOR.ClassObligation.half_one`
- `Rule30UOR.ClassObligation.half_zero`
- `Rule30UOR.ClassObligation.kappaCollapse_lateTail_flip`
- `Rule30UOR.ClassObligation.lag2_ge_two`
- `Rule30UOR.ClassObligation.lag2_zero`
- `Rule30UOR.ClassObligation.lag4_ge_four`
- `Rule30UOR.ClassObligation.lag4_one`
- `Rule30UOR.ClassObligation.lag4_two`
- `Rule30UOR.ClassObligation.lag4_zero`
- `Rule30UOR.ClassObligation.lateTail_obligation`
- `Rule30UOR.ClassObligation.lateTail_one_at_one`
- `Rule30UOR.ClassObligation.lateTail_one_at_one_cell`
- `Rule30UOR.ClassObligation.lateTail_scale`
- `Rule30UOR.ClassObligation.lateTail_three_at_one_cells`
- `Rule30UOR.ClassObligation.lateTail_three_dyadic_flip`
- … 1827 more

### `Rule30UOR.Scale.response` (82)
- `Rule30UOR.Automatic.dyadic_column_step`
- `Rule30UOR.Automatic.kernelSeq_step`
- `Rule30UOR.Automatic.response_cone`
- `Rule30UOR.Automatic.unflipped_succ`
- `Rule30UOR.DyadicRow.response_twopow_eq_not_blockParity`
- `Rule30UOR.Gasket.dyadic_response_halves`
- `Rule30UOR.Gasket.dyadic_response_halves_paper`
- `Rule30UOR.Gasket.response_eq_duhamel`
- `Rule30UOR.Interfaces.center_from_late_responses`
- `Rule30UOR.Interfaces.crossCarry_colm1_outside_cone_at_white_late_center_via_response`
- `Rule30UOR.Interfaces.crossCarry_colm1_outside_cone_at_white_late_center_via_response_prop`
- `Rule30UOR.Interfaces.late_scale_center_antiperiodic_of_doubles`
- `Rule30UOR.Interfaces.late_scale_center_antiperiodic_of_doubles_prop`
- `Rule30UOR.Interfaces.late_scale_center_periodic_of_doubles_le`
- `Rule30UOR.Interfaces.late_scale_center_periodic_of_doubles_le_prop`
- `Rule30UOR.Interfaces.late_scale_center_reset_antiperiodic_of_doubles`
- `Rule30UOR.Interfaces.late_scale_center_reset_antiperiodic_of_doubles_prop`
- `Rule30UOR.Interfaces.ldiag_eq_response_coboundary`
- `Rule30UOR.Interfaces.ldiag_eq_response_coboundary_cone`
- `Rule30UOR.Interfaces.lhCenter_twopow_eq_late_scale_center`
- `Rule30UOR.Interfaces.lhCenter_twopow_eq_response_coboundary_cone`
- `Rule30UOR.Interfaces.periodic_coboundary_collapse`
- `Rule30UOR.Interfaces.periodic_late_response_defect_eq_of_doubles_le`
- `Rule30UOR.Interfaces.periodic_late_response_defect_eq_of_doubles_le_prop`
- `Rule30UOR.Interfaces.periodic_late_response_defect_flip_of_doubles`
- `Rule30UOR.Interfaces.periodic_late_response_defect_flip_of_doubles_prop`
- `Rule30UOR.Interfaces.periodic_late_response_eq_of_lag_eq`
- `Rule30UOR.Interfaces.periodic_late_response_flip_of_doubles_and_eq`
- `Rule30UOR.Interfaces.periodic_late_response_flip_of_doubles_and_eq_prop`
- `Rule30UOR.Interfaces.periodic_late_response_reset_defect_flip_of_doubles`
- `Rule30UOR.Interfaces.periodic_late_response_reset_defect_flip_of_doubles_prop`
- `Rule30UOR.Interfaces.periodic_late_response_reset_flip_of_doubles_and_eq`
- `Rule30UOR.Interfaces.periodic_late_response_reset_flip_of_doubles_and_eq_prop`
- `Rule30UOR.Interfaces.periodic_late_response_settled_decomp`
- `Rule30UOR.Interfaces.periodic_late_response_unsettled_decomp`
- `Rule30UOR.Interfaces.periodic_ldiag_shift_mul_eq_response_shift_mul`
- `Rule30UOR.Interfaces.periodic_lhCenter_twopow_defect_eq_response_defect`
- `Rule30UOR.Interfaces.periodic_response_after_zero_diag`
- `Rule30UOR.Interfaces.periodic_response_after_zero_diag_prop`
- `Rule30UOR.Interfaces.periodic_response_at_zero_diag`
- `Rule30UOR.Interfaces.periodic_response_at_zero_diag_prop`
- `Rule30UOR.Interfaces.periodic_response_defect_after_zero_diag_eq_not_lhCenter_twopow`
- `Rule30UOR.Interfaces.periodic_response_defect_after_zero_diag_eq_not_lhCenter_twopow_prop`
- `Rule30UOR.Interfaces.periodic_response_defect_at_zero_diag_eq_lhCenter_twopow`
- `Rule30UOR.Interfaces.periodic_response_defect_at_zero_diag_eq_lhCenter_twopow_prop`
- `Rule30UOR.Interfaces.periodic_response_eq_cone_mul`
- `Rule30UOR.Interfaces.periodic_response_eq_of_lag_eq`
- `Rule30UOR.Interfaces.periodic_response_eq_of_lhBandAgree_twopow`
- `Rule30UOR.Interfaces.periodic_response_eq_of_lhColAgree_one_twopow`
- `Rule30UOR.Interfaces.periodic_response_eq_of_maskparity_zero_agree_twopow`
- `Rule30UOR.Interfaces.periodic_response_eq_of_two_zero_diags`
- `Rule30UOR.Interfaces.periodic_response_eq_of_two_zero_diags_prop`
- `Rule30UOR.Interfaces.periodic_response_eq_of_white_center_rhCenter_one_twopow`
- `Rule30UOR.Interfaces.periodic_response_flip_at_twopow_mul`
- `Rule30UOR.Interfaces.periodic_response_flip_at_zero_diag_step_two`
- `Rule30UOR.Interfaces.periodic_response_flip_at_zero_diag_step_two_prop`
- `Rule30UOR.Interfaces.periodic_response_flip_of_two_zero_diags`
- `Rule30UOR.Interfaces.periodic_response_flip_of_two_zero_diags_prop`
- `Rule30UOR.Interfaces.periodic_response_shift_P`
- `Rule30UOR.Interfaces.periodic_zcenter_from_lag_and_late_response`
- … 22 more

## Handles (register note)

Named row by row by scale-free-rows: the response of the block [2^j, 2^(j+1)) is blockParity j, the XOR of the scale-free bits dyadicRow m over the block; Problem 1 follows if j -> blockParity j is not eventually periodic (problem1_of_blockParityAperiodic).


_Generated by `bin/r30 interface`; the register is the source._
