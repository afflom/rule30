# Interface: dyadic-response-aperiodic [open]

The responses on the dyadic diagonal, j -> response(2^j, j) (the window [2^j, 2^(j+1)) read at the center), are not eventually periodic.

Lean: `Rule30UOR.Automatic.DyadicResponseAperiodic`

## Chain from the root

- [?] problem1 — `Ruliology.CellularAutomata.Rule30Prize.Problem1`
- [✓] periodic-finite-kernel — `Rule30UOR.Automatic.centerKernelFinite_of_centerPeriodic`
- [✓] kernel-self-similarity — `Rule30UOR.Automatic.problem1_of_no_dyadic_self_similarity`
- [✓] dilation-reduction — `Rule30UOR.Automatic.problem1_of_dyadic_column_aperiodic`
- [✓] ledger-diagonal — `Rule30UOR.Ledger.centerPeriodic_iff_ledgerPeriodic`
- [✓] recurrent-central-collision — `Rule30UOR.Frontier.problem1_iff_noRecurrentCentralCollision`
- [✓] coupling-law — `Rule30UOR.WittDefect.center_periodic_of_coupling`
- [?] aperiodic-compensation
- [✓] horizon-certificate — `Rule30UOR.Horizon.horizon_thirty_two`
- [✓] kappa-collapse — `Rule30UOR.Automatic.kappaCollapse_iff`
- [✓] dyadic-response-reduction — `Rule30UOR.Automatic.problem1_of_dyadic_response_aperiodic`
- [?] dyadic-response-aperiodic — `Rule30UOR.Automatic.DyadicResponseAperiodic`

## Notions (labels)

- `Rule30UOR.Automatic.DyadicResponsePeriodic` — lexeme `r30.observation::dyadic-response-periodic`
- `Rule30UOR.Core.twopow` — lexeme `r30.scale::twopow`
- `Rule30UOR.Scale.response` — lexeme `r30.scale::response`

## Exact facts about each notion

### `Rule30UOR.Automatic.DyadicResponsePeriodic` (1)
- `Rule30UOR.Automatic.dyadicResponsePeriodic_of_dilationPeriodic`

### `Rule30UOR.Core.twopow` (1786)
- `Rule30UOR.Automatic.centerPeriodic_of_kappaCollapse`
- `Rule30UOR.Automatic.center_mod_of_kappaCollapse`
- `Rule30UOR.Automatic.center_recovered_at_scale`
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
- `Rule30UOR.Core.phiScale.eq_1`
- `Rule30UOR.Core.twopow.eq_1`
- `Rule30UOR.Core.twopow.eq_2`
- `Rule30UOR.Core.twopow.eq_def`
- `Rule30UOR.Core.twopow_succ`
- `Rule30UOR.Gasket.response_eq_duhamel`
- `Rule30UOR.Interfaces.add_five_le_twopow`
- `Rule30UOR.Interfaces.bit_frobDefect_row_late_eq_frobDefect_winWitt_sector_two_prop`
- `Rule30UOR.Interfaces.bit_frobDefect_row_late_eq_winWitt_sector_two_wronskian_prop`
- `Rule30UOR.Interfaces.bit_frobDefect_row_late_sector_one_center_slot_wronskian_prop`
- `Rule30UOR.Interfaces.bit_frobDefect_row_late_sector_one_eq_crossCarry_cone_prop`
- `Rule30UOR.Interfaces.bit_frobDefect_row_lt_twopow_prop`
- `Rule30UOR.Interfaces.bit_frobDefect_row_sector_one_prop`
- `Rule30UOR.Interfaces.bit_frobDefect_row_sector_one_restart_prop`
- `Rule30UOR.Interfaces.bit_frobDefect_row_sector_two_restart_prop`
- `Rule30UOR.Interfaces.bit_frobDefect_winWitt_sector_two_wronskian_prop`
- `Rule30UOR.Interfaces.bit_periodic_winWitt_sector_one_shift_P`
- `Rule30UOR.Interfaces.bit_winWitt_archimedean`
- `Rule30UOR.Interfaces.bit_winWitt_center_slot`
- `Rule30UOR.Interfaces.bit_winWitt_cone_step_sector_one_edge`
- `Rule30UOR.Interfaces.bit_winWitt_cone_step_unperturbed_sector_one_gap`
- `Rule30UOR.Interfaces.bit_winWitt_cone_step_unperturbed_sector_zero`
- `Rule30UOR.Interfaces.bit_winWitt_gt_two_mul`
- `Rule30UOR.Interfaces.bit_winWitt_late_triality`
- `Rule30UOR.Interfaces.bit_winWitt_late_triality_prop`
- `Rule30UOR.Interfaces.bit_winWitt_leading_bit_of_threshold`
- `Rule30UOR.Interfaces.bit_winWitt_left_ray`
- `Rule30UOR.Interfaces.bit_winWitt_left_settled_zero`
- `Rule30UOR.Interfaces.bit_winWitt_low`
- `Rule30UOR.Interfaces.bit_winWitt_lt_twopow`
- `Rule30UOR.Interfaces.bit_winWitt_middle_ray`
- `Rule30UOR.Interfaces.bit_winWitt_second_edge_zero`
- `Rule30UOR.Interfaces.bit_winWitt_sector_one_at_threshold`
- `Rule30UOR.Interfaces.bit_winWitt_sector_one_below_threshold`
- `Rule30UOR.Interfaces.bit_winWitt_sector_one_cone`
- `Rule30UOR.Interfaces.bit_winWitt_sector_one_cone_edge`
- `Rule30UOR.Interfaces.bit_winWitt_sector_one_gap_ldiag`
- `Rule30UOR.Interfaces.bit_winWitt_sector_one_ldiag`
- `Rule30UOR.Interfaces.bit_winWitt_sector_one_settled`
- `Rule30UOR.Interfaces.bit_winWitt_sector_two_scale_eq`
- `Rule30UOR.Interfaces.bit_winWitt_third_edge_zero`
- `Rule30UOR.Interfaces.bit_winWitt_threshold_plus_two_collision_freeze`
- `Rule30UOR.Interfaces.bit_winWitt_threshold_plus_two_step_neg`
- `Rule30UOR.Interfaces.bit_winWitt_top_edge_zero`
- … 1726 more

### `Rule30UOR.Scale.response` (79)
- `Rule30UOR.Automatic.center_recovered_at_scale`
- `Rule30UOR.Automatic.dyadic_column_step`
- `Rule30UOR.Automatic.kernelSeq_step`
- `Rule30UOR.Automatic.response_cone`
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
- `Rule30UOR.Interfaces.periodic_zcenter_from_lag_and_late_response_prop`
- `Rule30UOR.Interfaces.periodic_zcenter_shift_xor_eq_late_response_xor`
- `Rule30UOR.Interfaces.periodic_zcenter_shift_xor_eq_late_response_xor_prop`
- … 19 more

## Handles (register note)

Sufficient for Problem 1 (dyadic-response-reduction). response(2^j, j) = window60 (2^j) (2^j) 0 is out of the cone; by wittRespBool_xor_response_ge it is the complement of wittRespBool(2^j, j), the ledger of the second dyadic block read at the diagonal. Exact handles: duhamel (cell(t0 + n) = Lpow n (cell t0) XOR window60 t0 n, with L the Rule-60 operator xor(x(p-1), x p)), freshman (Lpow (2^k) x p = x p XOR x (p - 2^k)), Lpow_add, and carry60 s p = (not cell s p) and cell s (p+1): the response is the Rule-60 (Sierpinski) propagation of the carry masks of the block [2^j, 2^(j+1)) read at the center, i.e. the parity of the carry-mask events on the gasket of the block. The 2-adic continuity caveat here reads: if response(2^j, j) were eventually 1 the column would be eventually constant. Next exact theorem: the binary (Lucas) product form of Lpow n from Lpow_add and freshman, giving the gasket explicitly. Not known.


_Generated by `bin/r30 interface`; the register is the source._
