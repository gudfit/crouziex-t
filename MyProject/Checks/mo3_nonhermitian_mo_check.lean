import MyProject.MO3NonHermitian

noncomputable section

namespace MyProject.Checks

-- Fast local checker for the concrete N=3 non-Hermitian MO block.
-- Run with:
--   lake env lean MyProject/Checks/mo3_nonhermitian_mo_check.lean

#check MO3Deg2Coeffs
#check w_MO3_deg2
#check w_MO3_deg2_mem_shiftedSpan3
#check w_MO_mem_shiftedSpan3_A3Shifted_deg2
#check MO3RawQuadCoeffs
#check ShiftedSpan3Coeffs
#check HasShiftedQuadDecomp
#check hasShiftedQuadDecomp_of_span_eq_top
#check w_MO3_raw_quad
#check w_MO3_raw_quad_reduction
#check w_MO3_raw_quad_mem_shiftedSpan3_of_coeff_decomp
#check w_MO3_raw_quad_mem_shiftedSpan3
#check MO3FirstVariationQuadCoeffs
#check MO3FirstVariationQuadCoeffs.toRaw
#check w_MO3_firstVariation_quad
#check w_MO3_firstVariation_quad_eq_deg2_of_coeff_decomp
#check w_MO3_firstVariation_quad_mem_shiftedSpan3
#check MO3QuadraticSetup
#check firstVariation_quad_orthogonal
#check firstVariation_quad_orthogonal_of_span_eq_top
#check dA2Witness
#check dAstarAWitness
#check A3SqLin_xWitness_eq_shiftedLinComb
#check A3AdjALin_xWitness_eq_shiftedLinComb
#check hasShiftedQuadDecomp_xWitness
#check w_MO3_raw_quad_mem_shiftedSpan3_xWitness
#check xBad
#check A3SqLin_xBad_not_mem_shiftedSpan3
#check not_hasShiftedQuadDecomp_xBad
#check not_forall_hasShiftedQuadDecomp
#check xiBad
#check rawA2Only
#check fvA2Only
#check not_unconditional_raw_quad_orthogonality
#check exists_raw_quad_orthogonality_counterexample
#check raw_quad_orthogonal_of_hasShiftedQuadDecomp
#check not_unconditional_firstVariation_quad_orthogonality
#check exists_firstVariation_quad_orthogonality_counterexample

#check shiftedSpan3_eq_moSpan3
#check mo3_nonhermitian_witness_package

def demoCoeffs : MO3Deg2Coeffs :=
  { a0 := 1
    a1 := alphaSqrtTwoMO
    a2 := (0 : ℂ)
    b0 := (0 : ℂ)
    b1 := (1 : ℂ)
    b2 := (-1 : ℂ) }

example : w_MO3_deg2 xWitness demoCoeffs ∈ shiftedSpan3 xWitness :=
  w_MO_mem_shiftedSpan3_A3Shifted_deg2 xWitness demoCoeffs

example : w_MO3_deg2 xWitness demoCoeffs ∈ moSpan3 xWitness := by
  have hmem : w_MO3_deg2 xWitness demoCoeffs ∈ shiftedSpan3 xWitness :=
    w_MO_mem_shiftedSpan3_A3Shifted_deg2 xWitness demoCoeffs
  rw [shiftedSpan3_eq_moSpan3 xWitness] at hmem
  exact hmem

example (x : E3MO) (raw : MO3RawQuadCoeffs) (hdecomp : HasShiftedQuadDecomp x) :
    w_MO3_raw_quad x raw ∈ shiftedSpan3 x :=
  w_MO3_raw_quad_mem_shiftedSpan3 x raw hdecomp

example (raw : MO3RawQuadCoeffs) :
    w_MO3_raw_quad xWitness raw ∈ shiftedSpan3 xWitness :=
  w_MO3_raw_quad_mem_shiftedSpan3_xWitness raw

def demoFV : MO3FirstVariationQuadCoeffs :=
  { c00 := 1
    c10 := alphaSqrtTwoMO
    c01 := (-1 : ℂ)
    c20 := (2 : ℂ)
    c11 := (3 : ℂ) }

example : w_MO3_firstVariation_quad xWitness demoFV ∈ shiftedSpan3 xWitness :=
  w_MO3_firstVariation_quad_mem_shiftedSpan3 xWitness demoFV hasShiftedQuadDecomp_xWitness

example :
    inner ℂ (w_MO3_firstVariation_quad xWitness demoFV) (0 : E3MO) = 0 := by
  have hsetup : MO3QuadraticSetup xWitness (0 : E3MO) := by
    refine ⟨hasShiftedQuadDecomp_xWitness, ?_⟩
    simp [Submodule.mem_orthogonal]
  simpa using firstVariation_quad_orthogonal xWitness (0 : E3MO) demoFV hsetup

example : ¬ (∀ x : E3MO, HasShiftedQuadDecomp x) :=
  not_forall_hasShiftedQuadDecomp

end MyProject.Checks
