import MyProject.MO4NonHermitian

noncomputable section

namespace MyProject.Checks

-- Fast local checker for the concrete N=4 non-Hermitian MO counterexample block.
-- Run with:
--   lake env lean MyProject/Checks/mo4_nonhermitian_mo_check.lean

#check E4MO
#check K4
#check A4Shifted
#check A4Lin
#check A4AdjLin
#check shiftedSpan4
#check A4SqLin
#check xBad4
#check A4Lin_xBad4
#check A4AdjLin_xBad4
#check A4SqLin_xBad4
#check shiftedSpan4_xBad4_second_zero
#check A4SqLin_xBad4_not_mem_shiftedSpan4
#check not_forall_A4SqLin_mem_shiftedSpan4
#check exists_A4SqLin_not_mem_shiftedSpan4
#check xiBad4
#check A4PowAct
#check A4AdjPowAct
#check coeffAt4
#check cjkFromCoeff4
#check mo4MultilinearD3
#check mo4MultilinearD3Exact
#check MO4D3ExactUnconditional
#check MO4CubicSetup
#check mo4MultilinearD3Exact_re_zero_of_setup
#check z3Coeffs4
#check mo4MultilinearZ3
#check mo4MultilinearD3Exact_z3_eq
#check xiBad4_mem_orthogonal_shiftedSpan4_xBad4
#check mo4MultilinearZ3_xBad4_xBad4_xiBad4
#check mo4MultilinearD3Exact_z3_xBad4_xBad4_xiBad4_re_pos
#check mo4MultilinearD3Exact_xBad4_scaled_xiBad4
#check mo4MultilinearD3Exact_xBad4_scaled_xiBad4_re_pos_of_topCoeff_ne_zero
#check not_unconditional_mo4_d3_exact_of_topCoeff_ne_zero
#check exists_mo4_d3_exact_counterexample_of_topCoeff_ne_zero
#check not_forall_coeffs_unconditional_mo4_d3_exact
#check not_unconditional_mo4_d3_exact_z3
#check exists_mo4_d3_exact_z3_counterexample

example : ¬ (∀ x : E4MO, A4SqLin x ∈ shiftedSpan4 x) :=
  not_forall_A4SqLin_mem_shiftedSpan4

end MyProject.Checks
