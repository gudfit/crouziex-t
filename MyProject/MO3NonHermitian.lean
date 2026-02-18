import MyProject.Basic

noncomputable section

namespace MyProject

abbrev E3MO := EuclideanSpace ℂ (Fin 3)

abbrev K3 : Matrix (Fin 3) (Fin 3) ℂ := CrabbMatrix 3

abbrev K3Lin : E3MO →ₗ[ℂ] E3MO := Matrix.toEuclideanLin K3

abbrev K3AdjLin : E3MO →ₗ[ℂ] E3MO := Matrix.toEuclideanLin K3.conjTranspose

def moSpan3 (x : E3MO) : Submodule ℂ E3MO :=
  Submodule.span ℂ ({x, K3Lin x, K3AdjLin x} : Set E3MO)

lemma mem_moSpan3_x (x : E3MO) : x ∈ moSpan3 x := by
  change x ∈ Submodule.span ℂ ({x, K3Lin x, K3AdjLin x} : Set E3MO)
  exact Submodule.subset_span (by simp)

lemma mem_moSpan3_Kx (x : E3MO) : K3Lin x ∈ moSpan3 x := by
  change K3Lin x ∈ Submodule.span ℂ ({x, K3Lin x, K3AdjLin x} : Set E3MO)
  exact Submodule.subset_span (by simp)

lemma mem_moSpan3_Kstarx (x : E3MO) : K3AdjLin x ∈ moSpan3 x := by
  change K3AdjLin x ∈ Submodule.span ℂ ({x, K3Lin x, K3AdjLin x} : Set E3MO)
  exact Submodule.subset_span (by simp)

lemma k3_entry_01 : K3 0 1 = (Real.sqrt 2 : ℂ) := by
  simp [K3, CrabbMatrix, crabbWeight]

lemma k3_entry_10 : K3 1 0 = 0 := by
  simp [K3, CrabbMatrix]

lemma k3_not_hermitian : ¬ K3.IsHermitian := by
  intro hH
  have h01_zero : K3 0 1 = 0 := by
    have h := hH.apply 0 1
    simpa [k3_entry_10] using h.symm
  have hsqrtR : (0 : ℝ) < Real.sqrt 2 := by positivity
  have hsqrt : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hsqrtR)
  exact hsqrt (k3_entry_01.symm.trans h01_zero)

noncomputable def alphaSqrtTwoMO : ℂ := (1 + Real.sqrt 2 : ℂ)

/-- Concrete non-Hermitian shifted/scaled Crabb matrix `I - αK_3`. -/
abbrev A3Shifted : Matrix (Fin 3) (Fin 3) ℂ :=
  (1 : Matrix (Fin 3) (Fin 3) ℂ) - alphaSqrtTwoMO • K3

/-- Linear action of `A3Shifted`. -/
abbrev A3Lin : E3MO →ₗ[ℂ] E3MO := Matrix.toEuclideanLin A3Shifted

/-- Linear action of `A3Shiftedᴴ`. -/
abbrev A3AdjLin : E3MO →ₗ[ℂ] E3MO := Matrix.toEuclideanLin A3Shifted.conjTranspose

/-- Shifted-span version `span{x, Ax, A* x}` for `A = I - αK_3`. -/
def shiftedSpan3 (x : E3MO) : Submodule ℂ E3MO :=
  Submodule.span ℂ ({x, A3Lin x, A3AdjLin x} : Set E3MO)

/-- Coefficients for the degree-2 (`N=3`) non-Hermitian MO variation template. -/
structure MO3Deg2Coeffs where
  a0 : ℂ
  a1 : ℂ
  a2 : ℂ
  b0 : ℂ
  b1 : ℂ
  b2 : ℂ

/--
Concrete `N=3` non-Hermitian MO variation vector for `A3Shifted`.
This is the compressed degree-2 ansatz in the 3D span `{x, Ax, A* x}`.
-/
def w_MO3_deg2 (x : E3MO) (coeff : MO3Deg2Coeffs) : E3MO :=
  (coeff.a0 + coeff.b0) • x +
    (coeff.a1 + coeff.b1) • A3Lin x +
    (coeff.a2 + coeff.b2) • A3AdjLin x

lemma w_MO3_deg2_mem_shiftedSpan3 (x : E3MO) (coeff : MO3Deg2Coeffs) :
    w_MO3_deg2 x coeff ∈ shiftedSpan3 x := by
  have hx : x ∈ shiftedSpan3 x := Submodule.subset_span (by simp)
  have hAx : A3Lin x ∈ shiftedSpan3 x := Submodule.subset_span (by simp)
  have hAstarx : A3AdjLin x ∈ shiftedSpan3 x := Submodule.subset_span (by simp)
  have h0 : (coeff.a0 + coeff.b0) • x ∈ shiftedSpan3 x :=
    Submodule.smul_mem (shiftedSpan3 x) _ hx
  have h1 : (coeff.a1 + coeff.b1) • A3Lin x ∈ shiftedSpan3 x :=
    Submodule.smul_mem (shiftedSpan3 x) _ hAx
  have h2 : (coeff.a2 + coeff.b2) • A3AdjLin x ∈ shiftedSpan3 x :=
    Submodule.smul_mem (shiftedSpan3 x) _ hAstarx
  have h12 :
      (coeff.a1 + coeff.b1) • A3Lin x + (coeff.a2 + coeff.b2) • A3AdjLin x
        ∈ shiftedSpan3 x :=
    Submodule.add_mem (shiftedSpan3 x) h1 h2
  have h012 :
      (coeff.a0 + coeff.b0) • x +
          ((coeff.a1 + coeff.b1) • A3Lin x + (coeff.a2 + coeff.b2) • A3AdjLin x)
        ∈ shiftedSpan3 x :=
    Submodule.add_mem (shiftedSpan3 x) h0 h12
  simpa [w_MO3_deg2, add_assoc] using h012

/-- Degree-2 `w_MO` membership statement for the shifted Crabb test matrix `A3Shifted`. -/
theorem w_MO_mem_shiftedSpan3_A3Shifted_deg2 (x : E3MO) (coeff : MO3Deg2Coeffs) :
    w_MO3_deg2 x coeff ∈ shiftedSpan3 x :=
  w_MO3_deg2_mem_shiftedSpan3 x coeff

/-- `A^2` action for the shifted test matrix. -/
def A3SqLin (x : E3MO) : E3MO := A3Lin (A3Lin x)

/-- Mixed `A* A` action for the shifted test matrix. -/
def A3AdjALin (x : E3MO) : E3MO := A3AdjLin (A3Lin x)

/-- Raw quadratic (`N=3`) coefficients before compression. -/
structure MO3RawQuadCoeffs where
  c0 : ℂ
  cA : ℂ
  cAstar : ℂ
  cA2 : ℂ
  cAstarA : ℂ

/-- Coefficients for a linear combination in `span{x, Ax, A* x}`. -/
structure ShiftedSpan3Coeffs where
  cx : ℂ
  cAx : ℂ
  cAstarx : ℂ

/-- Explicit linear combination in the shifted 3D span basis. -/
def shiftedLinComb (x : E3MO) (d : ShiftedSpan3Coeffs) : E3MO :=
  d.cx • x + d.cAx • A3Lin x + d.cAstarx • A3AdjLin x

lemma shiftedLinComb_mem_shiftedSpan3 (x : E3MO) (d : ShiftedSpan3Coeffs) :
    shiftedLinComb x d ∈ shiftedSpan3 x := by
  have hx : x ∈ shiftedSpan3 x := Submodule.subset_span (by simp)
  have hAx : A3Lin x ∈ shiftedSpan3 x := Submodule.subset_span (by simp)
  have hAstarx : A3AdjLin x ∈ shiftedSpan3 x := Submodule.subset_span (by simp)
  have h0 : d.cx • x ∈ shiftedSpan3 x := Submodule.smul_mem (shiftedSpan3 x) _ hx
  have h1 : d.cAx • A3Lin x ∈ shiftedSpan3 x := Submodule.smul_mem (shiftedSpan3 x) _ hAx
  have h2 : d.cAstarx • A3AdjLin x ∈ shiftedSpan3 x :=
    Submodule.smul_mem (shiftedSpan3 x) _ hAstarx
  exact Submodule.add_mem (shiftedSpan3 x) (Submodule.add_mem (shiftedSpan3 x) h0 h1) h2

/--
Raw quadratic MO variation: base terms plus higher terms `A^2 x` and `A* A x`.
This is the uncompressed object before projecting/reducing back to 3D.
-/
def w_MO3_raw_quad (x : E3MO) (raw : MO3RawQuadCoeffs) : E3MO :=
  raw.c0 • x +
    raw.cA • A3Lin x +
    raw.cAstar • A3AdjLin x +
    raw.cA2 • A3SqLin x +
    raw.cAstarA • A3AdjALin x

/-- Raw quadratic variation with `A^2x` and `A*Ax` already replaced by 3D combinations. -/
def w_MO3_raw_quad_reduced
    (x : E3MO) (raw : MO3RawQuadCoeffs) (dA2 dAstarA : ShiftedSpan3Coeffs) : E3MO :=
  raw.c0 • x +
    raw.cA • A3Lin x +
    raw.cAstar • A3AdjLin x +
    raw.cA2 • shiftedLinComb x dA2 +
    raw.cAstarA • shiftedLinComb x dAstarA

/-- Convert raw quadratic coefficients and decomposition data into compressed degree-2 coefficients. -/
def reduceRawQuadToDeg2
    (raw : MO3RawQuadCoeffs) (dA2 dAstarA : ShiftedSpan3Coeffs) : MO3Deg2Coeffs where
  a0 := raw.c0 + raw.cA2 * dA2.cx + raw.cAstarA * dAstarA.cx
  a1 := raw.cA + raw.cA2 * dA2.cAx + raw.cAstarA * dAstarA.cAx
  a2 := raw.cAstar + raw.cA2 * dA2.cAstarx + raw.cAstarA * dAstarA.cAstarx
  b0 := 0
  b1 := 0
  b2 := 0

lemma w_MO3_raw_quad_reduced_eq_w_MO3_deg2
    (x : E3MO) (raw : MO3RawQuadCoeffs) (dA2 dAstarA : ShiftedSpan3Coeffs) :
    w_MO3_raw_quad_reduced x raw dA2 dAstarA =
      w_MO3_deg2 x (reduceRawQuadToDeg2 raw dA2 dAstarA) := by
  ext i
  simp [w_MO3_raw_quad_reduced, w_MO3_deg2, reduceRawQuadToDeg2, shiftedLinComb, smul_eq_mul]
  ring

/--
Reduction lemma: once `A^2x` and `A*Ax` are decomposed in `span{x, Ax, A* x}`,
the raw quadratic variation equals a compressed degree-2 variation.
-/
theorem w_MO3_raw_quad_reduction
    (x : E3MO) (raw : MO3RawQuadCoeffs) (dA2 dAstarA : ShiftedSpan3Coeffs)
    (hA2 : A3SqLin x = shiftedLinComb x dA2)
    (hAstarA : A3AdjALin x = shiftedLinComb x dAstarA) :
    w_MO3_raw_quad x raw =
      w_MO3_deg2 x (reduceRawQuadToDeg2 raw dA2 dAstarA) := by
  rw [w_MO3_raw_quad, hA2, hAstarA]
  exact w_MO3_raw_quad_reduced_eq_w_MO3_deg2 x raw dA2 dAstarA

/-- Consequence of the reduction: raw quadratic variation lies in `shiftedSpan3`. -/
theorem w_MO3_raw_quad_mem_shiftedSpan3_of_coeff_decomp
    (x : E3MO) (raw : MO3RawQuadCoeffs) (dA2 dAstarA : ShiftedSpan3Coeffs)
    (hA2 : A3SqLin x = shiftedLinComb x dA2)
    (hAstarA : A3AdjALin x = shiftedLinComb x dAstarA) :
    w_MO3_raw_quad x raw ∈ shiftedSpan3 x := by
  rw [w_MO3_raw_quad_reduction x raw dA2 dAstarA hA2 hAstarA]
  exact w_MO_mem_shiftedSpan3_A3Shifted_deg2 x (reduceRawQuadToDeg2 raw dA2 dAstarA)

/-- Generic hypothesis package: both quadratic terms lie in `shiftedSpan3 x`. -/
structure HasShiftedQuadDecomp (x : E3MO) : Prop where
  hA2_mem : A3SqLin x ∈ shiftedSpan3 x
  hAstarA_mem : A3AdjALin x ∈ shiftedSpan3 x

/--
Generic constructor: if `span{x, Ax, A* x}` is all of `E3`, then both quadratic terms
automatically admit a `3D` decomposition.
-/
theorem hasShiftedQuadDecomp_of_span_eq_top
    (x : E3MO) (hspan : shiftedSpan3 x = ⊤) : HasShiftedQuadDecomp x := by
  refine ⟨?_, ?_⟩
  · simpa [hspan]
  · simpa [hspan]

/-- Raw quadratic membership using a bundled generic decomposition hypothesis on `x`. -/
theorem w_MO3_raw_quad_mem_shiftedSpan3
    (x : E3MO) (raw : MO3RawQuadCoeffs)
    (hdecomp : HasShiftedQuadDecomp x) :
    w_MO3_raw_quad x raw ∈ shiftedSpan3 x := by
  have hx : x ∈ shiftedSpan3 x := Submodule.subset_span (by simp)
  have hAx : A3Lin x ∈ shiftedSpan3 x := Submodule.subset_span (by simp)
  have hAstarx : A3AdjLin x ∈ shiftedSpan3 x := Submodule.subset_span (by simp)
  have h0 : raw.c0 • x ∈ shiftedSpan3 x := Submodule.smul_mem (shiftedSpan3 x) _ hx
  have h1 : raw.cA • A3Lin x ∈ shiftedSpan3 x := Submodule.smul_mem (shiftedSpan3 x) _ hAx
  have h2 : raw.cAstar • A3AdjLin x ∈ shiftedSpan3 x :=
    Submodule.smul_mem (shiftedSpan3 x) _ hAstarx
  have h3 : raw.cA2 • A3SqLin x ∈ shiftedSpan3 x :=
    Submodule.smul_mem (shiftedSpan3 x) _ hdecomp.hA2_mem
  have h4 : raw.cAstarA • A3AdjALin x ∈ shiftedSpan3 x :=
    Submodule.smul_mem (shiftedSpan3 x) _ hdecomp.hAstarA_mem
  have h01 : raw.c0 • x + raw.cA • A3Lin x ∈ shiftedSpan3 x :=
    Submodule.add_mem (shiftedSpan3 x) h0 h1
  have h012 : raw.c0 • x + raw.cA • A3Lin x + raw.cAstar • A3AdjLin x ∈ shiftedSpan3 x :=
    Submodule.add_mem (shiftedSpan3 x) h01 h2
  have h0123 :
      raw.c0 • x + raw.cA • A3Lin x + raw.cAstar • A3AdjLin x + raw.cA2 • A3SqLin x
        ∈ shiftedSpan3 x :=
    Submodule.add_mem (shiftedSpan3 x) h012 h3
  have h01234 :
      raw.c0 • x + raw.cA • A3Lin x + raw.cAstar • A3AdjLin x + raw.cA2 • A3SqLin x +
          raw.cAstarA • A3AdjALin x
        ∈ shiftedSpan3 x :=
    Submodule.add_mem (shiftedSpan3 x) h0123 h4
  simpa [w_MO3_raw_quad, add_assoc] using h01234

/-- Coefficients for the concrete quadratic first-variation (`p,q ≤ 2` truncated to `N=3`). -/
structure MO3FirstVariationQuadCoeffs where
  c00 : ℂ
  c10 : ℂ
  c01 : ℂ
  c20 : ℂ
  c11 : ℂ

/-- Convert first-variation coefficient data into the raw quadratic template coefficients. -/
def MO3FirstVariationQuadCoeffs.toRaw (fv : MO3FirstVariationQuadCoeffs) : MO3RawQuadCoeffs where
  c0 := fv.c00
  cA := fv.c10
  cAstar := fv.c01
  cA2 := fv.c20
  cAstarA := fv.c11

/--
Concrete quadratic first-variation vector for the non-Hermitian `A3Shifted` setting.
This is the `N=3` object containing terms `x`, `Ax`, `A* x`, `A^2 x`, `A* A x`.
-/
def w_MO3_firstVariation_quad (x : E3MO) (fv : MO3FirstVariationQuadCoeffs) : E3MO :=
  w_MO3_raw_quad x fv.toRaw

lemma w_MO3_firstVariation_quad_eq_raw (x : E3MO) (fv : MO3FirstVariationQuadCoeffs) :
    w_MO3_firstVariation_quad x fv = w_MO3_raw_quad x fv.toRaw := rfl

lemma w_MO3_firstVariation_quad_eq_deg2_of_coeff_decomp
    (x : E3MO) (fv : MO3FirstVariationQuadCoeffs) (dA2 dAstarA : ShiftedSpan3Coeffs)
    (hA2 : A3SqLin x = shiftedLinComb x dA2)
    (hAstarA : A3AdjALin x = shiftedLinComb x dAstarA) :
    w_MO3_firstVariation_quad x fv =
      w_MO3_deg2 x (reduceRawQuadToDeg2 fv.toRaw dA2 dAstarA) := by
  simpa [w_MO3_firstVariation_quad] using
    (w_MO3_raw_quad_reduction x fv.toRaw dA2 dAstarA hA2 hAstarA)

lemma w_MO3_firstVariation_quad_mem_shiftedSpan3
    (x : E3MO) (fv : MO3FirstVariationQuadCoeffs)
    (hdecomp : HasShiftedQuadDecomp x) :
    w_MO3_firstVariation_quad x fv ∈ shiftedSpan3 x := by
  simpa [w_MO3_firstVariation_quad] using
    (w_MO3_raw_quad_mem_shiftedSpan3 x fv.toRaw hdecomp)

/-- Generic non-Hermitian quadratic MO setup for the first-variation orthogonality statement. -/
structure MO3QuadraticSetup (x ξ : E3MO) : Prop where
  h_decomp : HasShiftedQuadDecomp x
  h_ξ_orth : ξ ∈ (shiftedSpan3 x)ᗮ

/--
Quadratic first-variation vanishing against any test vector orthogonal to `span{x, Ax, A* x}`.
This is the concrete `N=3` non-Hermitian orthogonality statement for `A3Shifted`.
-/
theorem firstVariation_quad_orthogonal
    (x ξ : E3MO) (fv : MO3FirstVariationQuadCoeffs)
    (hsetup : MO3QuadraticSetup x ξ) :
    inner ℂ (w_MO3_firstVariation_quad x fv) ξ = 0 := by
  have hw : w_MO3_firstVariation_quad x fv ∈ shiftedSpan3 x :=
    w_MO3_firstVariation_quad_mem_shiftedSpan3 x fv hsetup.h_decomp
  exact (Submodule.mem_orthogonal (shiftedSpan3 x) ξ).1 hsetup.h_ξ_orth
    (w_MO3_firstVariation_quad x fv) hw

theorem firstVariation_quad_orthogonal_of_span_eq_top
    (x ξ : E3MO) (fv : MO3FirstVariationQuadCoeffs)
    (hspan : shiftedSpan3 x = ⊤)
    (hξ : ξ ∈ (shiftedSpan3 x)ᗮ) :
    inner ℂ (w_MO3_firstVariation_quad x fv) ξ = 0 := by
  have hdecomp : HasShiftedQuadDecomp x := hasShiftedQuadDecomp_of_span_eq_top x hspan
  exact firstVariation_quad_orthogonal x ξ fv ⟨hdecomp, hξ⟩

lemma alphaSqrtTwoMO_ne_zero : alphaSqrtTwoMO ≠ 0 := by
  have hαR : (0 : ℝ) < 1 + Real.sqrt 2 := by positivity
  dsimp [alphaSqrtTwoMO]
  exact_mod_cast (ne_of_gt hαR)

lemma star_alphaSqrtTwoMO_ne_zero : star alphaSqrtTwoMO ≠ 0 := by
  intro h
  apply alphaSqrtTwoMO_ne_zero
  simpa using congrArg star h

lemma A3Lin_formula (x : E3MO) :
    A3Lin x = x - alphaSqrtTwoMO • K3Lin x := by
  ext i
  fin_cases i <;>
    simp [A3Lin, A3Shifted, K3Lin, alphaSqrtTwoMO, K3, CrabbMatrix, crabbWeight, Matrix.mulVec,
      dotProduct, Fin.sum_univ_three]

lemma A3AdjLin_formula (x : E3MO) :
    A3AdjLin x = x - star alphaSqrtTwoMO • K3AdjLin x := by
  ext i
  fin_cases i <;>
    simp [A3AdjLin, A3Shifted, K3AdjLin, alphaSqrtTwoMO, K3, CrabbMatrix, crabbWeight,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.conjTranspose_apply]

lemma shiftedSpan3_eq_moSpan3 (x : E3MO) : shiftedSpan3 x = moSpan3 x := by
  refine le_antisymm ?_ ?_
  · refine Submodule.span_le.mpr ?_
    intro y hy
    have hy' : y = x ∨ y = A3Lin x ∨ y = A3AdjLin x := by
      simpa [shiftedSpan3, Set.mem_insert_iff] using hy
    rcases hy' with rfl | hy''
    · simpa using (mem_moSpan3_x y)
    · rcases hy'' with rfl | rfl
      · rw [A3Lin_formula]
        exact Submodule.sub_mem (moSpan3 x) (mem_moSpan3_x x)
          (Submodule.smul_mem (moSpan3 x) _ (mem_moSpan3_Kx x))
      · rw [A3AdjLin_formula]
        exact Submodule.sub_mem (moSpan3 x) (mem_moSpan3_x x)
          (Submodule.smul_mem (moSpan3 x) _ (mem_moSpan3_Kstarx x))
  · have hx_shift : x ∈ shiftedSpan3 x := by
      exact Submodule.subset_span (by simp)
    have hAx_shift : A3Lin x ∈ shiftedSpan3 x := by
      exact Submodule.subset_span (by simp)
    have hAstar_shift : A3AdjLin x ∈ shiftedSpan3 x := by
      exact Submodule.subset_span (by simp)
    have hAx_sub : A3Lin x - x = (-alphaSqrtTwoMO) • K3Lin x := by
      rw [A3Lin_formula]
      simp [sub_eq_add_neg, add_left_comm, add_comm]
    have hK_shift : K3Lin x ∈ shiftedSpan3 x := by
      have hsub : A3Lin x - x ∈ shiftedSpan3 x := Submodule.sub_mem _ hAx_shift hx_shift
      have hnegα : (-alphaSqrtTwoMO) ≠ 0 := neg_ne_zero.mpr alphaSqrtTwoMO_ne_zero
      have hk_eq : K3Lin x = (-alphaSqrtTwoMO)⁻¹ • (A3Lin x - x) := by
        rw [hAx_sub]
        simpa using (inv_smul_smul₀ hnegα (K3Lin x)).symm
      rw [hk_eq]
      exact Submodule.smul_mem (shiftedSpan3 x) _ hsub
    have hAstar_sub : A3AdjLin x - x = (-star alphaSqrtTwoMO) • K3AdjLin x := by
      rw [A3AdjLin_formula]
      simp [sub_eq_add_neg, add_left_comm, add_comm]
    have hKstar_shift : K3AdjLin x ∈ shiftedSpan3 x := by
      have hsub : A3AdjLin x - x ∈ shiftedSpan3 x := Submodule.sub_mem _ hAstar_shift hx_shift
      have hnegα : (-star alphaSqrtTwoMO) ≠ 0 := neg_ne_zero.mpr star_alphaSqrtTwoMO_ne_zero
      have hk_eq : K3AdjLin x = (-star alphaSqrtTwoMO)⁻¹ • (A3AdjLin x - x) := by
        rw [hAstar_sub]
        simpa using (inv_smul_smul₀ hnegα (K3AdjLin x)).symm
      rw [hk_eq]
      exact Submodule.smul_mem (shiftedSpan3 x) _ hsub
    refine Submodule.span_le.mpr ?_
    intro y hy
    have hy' : y = x ∨ y = K3Lin x ∨ y = K3AdjLin x := by
      simpa [moSpan3, Set.mem_insert_iff] using hy
    rcases hy' with rfl | hy''
    · exact hx_shift
    · rcases hy'' with rfl | rfl
      · exact hK_shift
      · exact hKstar_shift

lemma A3Shifted_not_hermitian : ¬ A3Shifted.IsHermitian := by
  intro hH
  have h10 : A3Shifted 1 0 = 0 := by
    simp [A3Shifted, alphaSqrtTwoMO, K3, CrabbMatrix]
  have h01 : A3Shifted 0 1 = -(alphaSqrtTwoMO * (Real.sqrt 2 : ℂ)) := by
    simp [A3Shifted, alphaSqrtTwoMO, K3, CrabbMatrix, crabbWeight]
  have hα : alphaSqrtTwoMO ≠ 0 := by
    have hαR : (0 : ℝ) < 1 + Real.sqrt 2 := by positivity
    dsimp [alphaSqrtTwoMO]
    exact_mod_cast (ne_of_gt hαR)
  have hsqrtR : (0 : ℝ) < Real.sqrt 2 := by positivity
  have hsqrt : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hsqrtR)
  have h01_ne : A3Shifted 0 1 ≠ 0 := by
    rw [h01]
    exact neg_ne_zero.mpr (mul_ne_zero hα hsqrt)
  have h01_zero : A3Shifted 0 1 = 0 := by
    have h := hH.apply 0 1
    simpa [h10] using h.symm
  exact h01_ne h01_zero

/-- Counterexample vector: unconditional `∀ x, HasShiftedQuadDecomp x` is false. -/
def xBad : E3MO := WithLp.toLp (p := 2) ![(1 : ℂ), 0, 1]

lemma A3Lin_xBad :
    A3Lin xBad = ![(1 : ℂ), -(alphaSqrtTwoMO * (Real.sqrt 2 : ℂ)), 1] := by
  ext i
  fin_cases i <;>
    simp [A3Lin, A3Shifted, xBad, alphaSqrtTwoMO, K3, CrabbMatrix, crabbWeight, Matrix.mulVec,
      dotProduct, Fin.sum_univ_three]

lemma A3AdjLin_xBad :
    A3AdjLin xBad = ![(1 : ℂ), -(star alphaSqrtTwoMO * (Real.sqrt 2 : ℂ)), 1] := by
  ext i
  fin_cases i <;>
    simp [A3AdjLin, A3Shifted, xBad, alphaSqrtTwoMO, K3, CrabbMatrix, crabbWeight, Matrix.mulVec,
      dotProduct, Fin.sum_univ_three, Matrix.conjTranspose_apply]

lemma A3SqLin_xBad :
    A3SqLin xBad =
      ![(1 : ℂ) + (2 : ℂ) * alphaSqrtTwoMO ^ 2, -(2 : ℂ) * alphaSqrtTwoMO * (Real.sqrt 2 : ℂ), 1] := by
  have hsq2 : ((Real.sqrt 2 : ℂ) ^ 2) = (2 : ℂ) := by
    have hsqR : (Real.sqrt 2) ^ 2 = 2 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by positivity)]
    exact_mod_cast hsqR
  rw [A3SqLin, A3Lin, matrix_toEuclideanLin_apply, A3Lin_xBad]
  ext i
  fin_cases i
  · simp [A3Shifted, K3, CrabbMatrix, crabbWeight, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      smul_eq_mul]
    calc
      alphaSqrtTwoMO * (Real.sqrt 2 : ℂ) * (alphaSqrtTwoMO * (Real.sqrt 2 : ℂ))
          = alphaSqrtTwoMO ^ 2 * ((Real.sqrt 2 : ℂ) ^ 2) := by ring
      _ = alphaSqrtTwoMO ^ 2 * (2 : ℂ) := by rw [hsq2]
      _ = (2 : ℂ) * alphaSqrtTwoMO ^ 2 := by ring
  · simp [A3Shifted, K3, CrabbMatrix, crabbWeight, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      smul_eq_mul]
    ring
  · simp [A3Shifted, K3, CrabbMatrix, crabbWeight, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      smul_eq_mul]

def firstEqThirdSubmodule : Submodule ℂ E3MO where
  carrier := {y | y.ofLp 0 = y.ofLp 2}
  zero_mem' := by simp
  add_mem' := by
    intro y z hy hz
    calc
      y.ofLp 0 + z.ofLp 0 = y.ofLp 2 + z.ofLp 0 := by rw [hy]
      _ = y.ofLp 2 + z.ofLp 2 := by rw [hz]
  smul_mem' := by
    intro a y hy
    exact congrArg (fun t : ℂ => a * t) hy

lemma A3Lin_xBad_first_eq_third : (A3Lin xBad).ofLp 0 = (A3Lin xBad).ofLp 2 := by
  have h0 : (A3Lin xBad).ofLp 0 = (1 : ℂ) := by
    simpa using congr_fun A3Lin_xBad 0
  have h2 : (A3Lin xBad).ofLp 2 = (1 : ℂ) := by
    simpa using congr_fun A3Lin_xBad 2
  calc
    (A3Lin xBad).ofLp 0 = (1 : ℂ) := h0
    _ = (A3Lin xBad).ofLp 2 := h2.symm

lemma A3AdjLin_xBad_first_eq_third : (A3AdjLin xBad).ofLp 0 = (A3AdjLin xBad).ofLp 2 := by
  have h0 : (A3AdjLin xBad).ofLp 0 = (1 : ℂ) := by
    simpa using congr_fun A3AdjLin_xBad 0
  have h2 : (A3AdjLin xBad).ofLp 2 = (1 : ℂ) := by
    simpa using congr_fun A3AdjLin_xBad 2
  calc
    (A3AdjLin xBad).ofLp 0 = (1 : ℂ) := h0
    _ = (A3AdjLin xBad).ofLp 2 := h2.symm

lemma shiftedSpan3_xBad_le_firstEqThird : shiftedSpan3 xBad ≤ firstEqThirdSubmodule := by
  refine Submodule.span_le.mpr ?_
  intro y hy
  have hy' : y = xBad ∨ y = A3Lin xBad ∨ y = A3AdjLin xBad := by
    simpa [shiftedSpan3, Set.mem_insert_iff] using hy
  rcases hy' with rfl | hy''
  · change xBad.ofLp 0 = xBad.ofLp 2
    simp [xBad]
  · rcases hy'' with rfl | rfl
    · exact A3Lin_xBad_first_eq_third
    · exact A3AdjLin_xBad_first_eq_third

lemma shiftedSpan3_xBad_first_eq_third (y : E3MO) (hy : y ∈ shiftedSpan3 xBad) :
    y.ofLp 0 = y.ofLp 2 := by
  exact (shiftedSpan3_xBad_le_firstEqThird hy)

lemma A3SqLin_xBad_first_ne_third :
    (A3SqLin xBad).ofLp 0 ≠ (A3SqLin xBad).ofLp 2 := by
  intro hEq
  have h0 : (A3SqLin xBad).ofLp 0 = (1 : ℂ) + (2 : ℂ) * alphaSqrtTwoMO ^ 2 := by
    simpa using congr_fun A3SqLin_xBad 0
  have h2 : (A3SqLin xBad).ofLp 2 = (1 : ℂ) := by
    simpa using congr_fun A3SqLin_xBad 2
  rw [h0, h2] at hEq
  have hEq' : (1 : ℂ) + (2 : ℂ) * alphaSqrtTwoMO ^ 2 = (1 : ℂ) + 0 := by simpa using hEq
  have hzero : (2 : ℂ) * alphaSqrtTwoMO ^ 2 = 0 := add_left_cancel hEq'
  have h2ne : (2 : ℂ) ≠ 0 := by norm_num
  have hpow : alphaSqrtTwoMO ^ 2 ≠ 0 := pow_ne_zero 2 alphaSqrtTwoMO_ne_zero
  exact (mul_ne_zero h2ne hpow) hzero

lemma A3SqLin_xBad_not_mem_shiftedSpan3 : A3SqLin xBad ∉ shiftedSpan3 xBad := by
  intro hmem
  exact A3SqLin_xBad_first_ne_third (shiftedSpan3_xBad_first_eq_third (A3SqLin xBad) hmem)

theorem not_hasShiftedQuadDecomp_xBad : ¬ HasShiftedQuadDecomp xBad := by
  intro h
  exact A3SqLin_xBad_not_mem_shiftedSpan3 h.hA2_mem

theorem not_forall_hasShiftedQuadDecomp : ¬ (∀ x : E3MO, HasShiftedQuadDecomp x) := by
  intro hAll
  exact not_hasShiftedQuadDecomp_xBad (hAll xBad)

/-- Orthogonal-direction witness used to refute a naive unconditional raw-quadratic MO statement. -/
def xiBad : E3MO := WithLp.toLp (p := 2) ![(1 : ℂ), 0, -1]

lemma inner_eq_star_first_sub_star_third_xiBad (y : E3MO) :
    inner ℂ y xiBad = star (y.ofLp 0) - star (y.ofLp 2) := by
  simp [xiBad, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_three,
    sub_eq_add_neg]

lemma xiBad_mem_orthogonal_shiftedSpan3_xBad : xiBad ∈ (shiftedSpan3 xBad)ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro y hy
  have hy03 : y.ofLp 0 = y.ofLp 2 := shiftedSpan3_xBad_first_eq_third y hy
  rw [inner_eq_star_first_sub_star_third_xiBad]
  simp [hy03]

lemma inner_A3SqLin_xBad_xiBad_ne_zero : inner ℂ (A3SqLin xBad) xiBad ≠ 0 := by
  rw [inner_eq_star_first_sub_star_third_xiBad]
  have h0 : (A3SqLin xBad).ofLp 0 = (1 : ℂ) + (2 : ℂ) * alphaSqrtTwoMO ^ 2 := by
    simpa using congr_fun A3SqLin_xBad 0
  have h2 : (A3SqLin xBad).ofLp 2 = (1 : ℂ) := by
    simpa using congr_fun A3SqLin_xBad 2
  rw [h0, h2]
  have h2ne : (2 : ℂ) ≠ 0 := by norm_num
  have hpow : alphaSqrtTwoMO ^ 2 ≠ 0 := pow_ne_zero 2 alphaSqrtTwoMO_ne_zero
  have hmul_ne : (2 : ℂ) * alphaSqrtTwoMO ^ 2 ≠ 0 := mul_ne_zero h2ne hpow
  have hneq : (1 : ℂ) + (2 : ℂ) * alphaSqrtTwoMO ^ 2 ≠ (1 : ℂ) := by
    intro hEq
    have hEq' : (1 : ℂ) + (2 : ℂ) * alphaSqrtTwoMO ^ 2 = (1 : ℂ) + 0 := by
      simpa using hEq
    have hzero : (2 : ℂ) * alphaSqrtTwoMO ^ 2 = 0 := add_left_cancel hEq'
    exact hmul_ne hzero
  have hneq_star :
      star ((1 : ℂ) + (2 : ℂ) * alphaSqrtTwoMO ^ 2) ≠ star (1 : ℂ) := by
    intro hEq
    have hEq2 : (1 : ℂ) + (2 : ℂ) * alphaSqrtTwoMO ^ 2 = (1 : ℂ) := by
      simpa using congrArg star hEq
    exact hneq hEq2
  exact sub_ne_zero.mpr hneq_star

/-- Raw coefficients selecting only the `A^2x` term. -/
def rawA2Only : MO3RawQuadCoeffs where
  c0 := 0
  cA := 0
  cAstar := 0
  cA2 := 1
  cAstarA := 0

lemma w_rawA2Only_eq_A3SqLin_xBad : w_MO3_raw_quad xBad rawA2Only = A3SqLin xBad := by
  ext i
  simp [w_MO3_raw_quad, rawA2Only, A3SqLin]

/--
A naive unconditional orthogonality claim for raw quadratic variations is false:
orthogonality of `ξ` to `span{x, Ax, A* x}` does not force
`inner (w_MO3_raw_quad x raw) ξ = 0` without additional decomposition assumptions.
-/
theorem not_unconditional_raw_quad_orthogonality :
    ¬ (∀ x ξ raw, ξ ∈ (shiftedSpan3 x)ᗮ → inner ℂ (w_MO3_raw_quad x raw) ξ = 0) := by
  intro h
  have hzero : inner ℂ (w_MO3_raw_quad xBad rawA2Only) xiBad = 0 :=
    h xBad xiBad rawA2Only xiBad_mem_orthogonal_shiftedSpan3_xBad
  rw [w_rawA2Only_eq_A3SqLin_xBad] at hzero
  exact inner_A3SqLin_xBad_xiBad_ne_zero hzero

theorem exists_raw_quad_orthogonality_counterexample :
    ∃ x ξ raw, ξ ∈ (shiftedSpan3 x)ᗮ ∧ inner ℂ (w_MO3_raw_quad x raw) ξ ≠ 0 := by
  refine ⟨xBad, xiBad, rawA2Only, xiBad_mem_orthogonal_shiftedSpan3_xBad, ?_⟩
  rw [w_rawA2Only_eq_A3SqLin_xBad]
  exact inner_A3SqLin_xBad_xiBad_ne_zero

/--
Corrected unconditional form: orthogonality holds for raw quadratic variations
once the quadratic decomposition hypothesis on `x` is included.
-/
theorem raw_quad_orthogonal_of_hasShiftedQuadDecomp
    (x ξ : E3MO) (raw : MO3RawQuadCoeffs)
    (hdecomp : HasShiftedQuadDecomp x)
    (hξ : ξ ∈ (shiftedSpan3 x)ᗮ) :
    inner ℂ (w_MO3_raw_quad x raw) ξ = 0 := by
  have hw : w_MO3_raw_quad x raw ∈ shiftedSpan3 x :=
    w_MO3_raw_quad_mem_shiftedSpan3 x raw hdecomp
  exact (Submodule.mem_orthogonal (shiftedSpan3 x) ξ).1 hξ _ hw

/-- First-variation coefficients selecting only the `A^2x` term. -/
def fvA2Only : MO3FirstVariationQuadCoeffs where
  c00 := 0
  c10 := 0
  c01 := 0
  c20 := 1
  c11 := 0

lemma w_fvA2Only_eq_A3SqLin_xBad : w_MO3_firstVariation_quad xBad fvA2Only = A3SqLin xBad := by
  ext i
  simp [w_MO3_firstVariation_quad, fvA2Only, MO3FirstVariationQuadCoeffs.toRaw,
    w_MO3_raw_quad, A3SqLin]

/--
The naive unconditional first-variation orthogonality claim is false:
without decomposition hypotheses, orthogonality of `ξ` to `span{x,Ax,A* x}`
does not force vanishing of `inner (w_MO3_firstVariation_quad x fv) ξ`.
-/
theorem not_unconditional_firstVariation_quad_orthogonality :
    ¬ (∀ x ξ fv, ξ ∈ (shiftedSpan3 x)ᗮ → inner ℂ (w_MO3_firstVariation_quad x fv) ξ = 0) := by
  intro h
  have hzero : inner ℂ (w_MO3_firstVariation_quad xBad fvA2Only) xiBad = 0 :=
    h xBad xiBad fvA2Only xiBad_mem_orthogonal_shiftedSpan3_xBad
  rw [w_fvA2Only_eq_A3SqLin_xBad] at hzero
  exact inner_A3SqLin_xBad_xiBad_ne_zero hzero

theorem exists_firstVariation_quad_orthogonality_counterexample :
    ∃ x ξ fv, ξ ∈ (shiftedSpan3 x)ᗮ ∧ inner ℂ (w_MO3_firstVariation_quad x fv) ξ ≠ 0 := by
  refine ⟨xBad, xiBad, fvA2Only, xiBad_mem_orthogonal_shiftedSpan3_xBad, ?_⟩
  rw [w_fvA2Only_eq_A3SqLin_xBad]
  exact inner_A3SqLin_xBad_xiBad_ne_zero

/-- Concrete witness vector for non-collapse checks. -/
def xWitness : E3MO := WithLp.toLp (p := 2) ![(1 : ℂ), 1, 0]

lemma K3Lin_xWitness :
    K3Lin xWitness = ![(Real.sqrt 2 : ℂ), 0, 0] := by
  ext i
  fin_cases i <;>
    simp [K3Lin, K3, xWitness, CrabbMatrix, crabbWeight, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three]

lemma K3AdjLin_xWitness :
    K3AdjLin xWitness = ![0, (Real.sqrt 2 : ℂ), (Real.sqrt 2 : ℂ)] := by
  ext i
  fin_cases i <;>
    simp [K3AdjLin, K3, xWitness, CrabbMatrix, crabbWeight, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three, Matrix.conjTranspose_apply]

lemma k3Adj_witness_not_mem_span_x_k3x :
    K3AdjLin xWitness ∉ Submodule.span ℂ ({xWitness, K3Lin xWitness} : Set E3MO) := by
  intro hmem
  rcases (Submodule.mem_span_pair.mp hmem) with ⟨a, b, hab⟩
  have h2 : (a • xWitness + b • K3Lin xWitness).ofLp 2 = (K3AdjLin xWitness).ofLp 2 := by
    exact congrArg (fun v : E3MO => v.ofLp 2) hab
  have hK3lin2 : (K3Lin xWitness).ofLp 2 = 0 := by
    simpa using congr_fun K3Lin_xWitness 2
  have hK3adj2 : (K3AdjLin xWitness).ofLp 2 = (Real.sqrt 2 : ℂ) := by
    simpa using congr_fun K3AdjLin_xWitness 2
  have h2' : a * (xWitness.ofLp 2) + b * (K3Lin xWitness).ofLp 2 = (K3AdjLin xWitness).ofLp 2 := by
    simpa [Pi.add_apply, smul_eq_mul] using h2
  have hsqrtR : (0 : ℝ) < Real.sqrt 2 := by positivity
  have hsqrt : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hsqrtR)
  rw [hK3lin2, hK3adj2] at h2'
  simp [xWitness] at h2'
  exact hsqrt h2'.symm

lemma A3Lin_xWitness :
    A3Lin xWitness = ![(1 : ℂ) - alphaSqrtTwoMO * (Real.sqrt 2 : ℂ), 1, 0] := by
  ext i
  fin_cases i <;>
    simp [A3Lin, A3Shifted, xWitness, alphaSqrtTwoMO, K3, CrabbMatrix, crabbWeight, Matrix.mulVec,
      dotProduct, Fin.sum_univ_three]

lemma A3AdjLin_xWitness :
    A3AdjLin xWitness =
      ![(1 : ℂ), (1 : ℂ) - star alphaSqrtTwoMO * (Real.sqrt 2 : ℂ),
        -(star alphaSqrtTwoMO * (Real.sqrt 2 : ℂ))] := by
  ext i
  fin_cases i <;>
    simp [A3AdjLin, A3Shifted, xWitness, alphaSqrtTwoMO, K3, CrabbMatrix, crabbWeight, Matrix.mulVec,
      dotProduct, Fin.sum_univ_three, Matrix.conjTranspose_apply]

/-- Explicit decomposition coefficients for `A^2 xWitness` in `span{x, Ax, A* x}`. -/
def dA2Witness : ShiftedSpan3Coeffs where
  cx := (-1 : ℂ)
  cAx := (2 : ℂ)
  cAstarx := 0

lemma A3SqLin_xWitness :
    (A3SqLin xWitness).ofLp = ![(1 : ℂ) - (2 : ℂ) * alphaSqrtTwoMO * (Real.sqrt 2 : ℂ), 1, 0] := by
  rw [A3SqLin, A3Lin, matrix_toEuclideanLin_apply, A3Lin_xWitness]
  ext i
  fin_cases i <;>
    simp [A3Shifted, K3, CrabbMatrix, crabbWeight, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      smul_eq_mul]
    <;> ring

lemma A3SqLin_xWitness_eq_shiftedLinComb :
    A3SqLin xWitness = shiftedLinComb xWitness dA2Witness := by
  have hSqE :
      A3SqLin xWitness =
        WithLp.toLp (p := 2) ![(1 : ℂ) - (2 : ℂ) * alphaSqrtTwoMO * (Real.sqrt 2 : ℂ), 1, 0] := by
    ext i
    simpa using congr_fun A3SqLin_xWitness i
  have hAxE :
      A3Lin xWitness =
        WithLp.toLp (p := 2) ![(1 : ℂ) - alphaSqrtTwoMO * (Real.sqrt 2 : ℂ), 1, 0] := by
    ext i
    simpa using congr_fun A3Lin_xWitness i
  rw [hSqE, shiftedLinComb, dA2Witness, hAxE]
  ext i
  fin_cases i <;>
    simp [xWitness, smul_eq_mul]
    <;> ring

/-- Explicit decomposition coefficients for `A* A xWitness` in `span{x, Ax, A* x}`. -/
def dAstarAWitness : ShiftedSpan3Coeffs where
  cx := (2 : ℂ) * alphaSqrtTwoMO ^ 2 - (1 + (Real.sqrt 2 : ℂ) * alphaSqrtTwoMO)
  cAx := 1 + (Real.sqrt 2 : ℂ) * alphaSqrtTwoMO
  cAstarx := 1

lemma A3AdjALin_xWitness :
    (A3AdjALin xWitness).ofLp =
      ![(1 : ℂ) - alphaSqrtTwoMO * (Real.sqrt 2 : ℂ),
        (1 : ℂ) - star alphaSqrtTwoMO * (Real.sqrt 2 : ℂ) +
          (2 : ℂ) * star alphaSqrtTwoMO * alphaSqrtTwoMO,
        -(star alphaSqrtTwoMO * (Real.sqrt 2 : ℂ))] := by
  have hsq2 : ((Real.sqrt 2 : ℂ) ^ 2) = (2 : ℂ) := by
    have hsqR : (Real.sqrt 2) ^ 2 = 2 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by positivity)]
    exact_mod_cast hsqR
  rw [A3AdjALin, A3AdjLin, matrix_toEuclideanLin_apply, A3Lin_xWitness]
  ext i
  fin_cases i
  · simp [A3Shifted, K3, CrabbMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      Matrix.conjTranspose_apply, smul_eq_mul]
  · simp [A3Shifted, K3, CrabbMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      Matrix.conjTranspose_apply, crabbWeight, smul_eq_mul]
    have hmul : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = (2 : ℂ) := by
      simpa [pow_two] using hsq2
    calc
      -((starRingEnd ℂ) alphaSqrtTwoMO * (Real.sqrt 2 : ℂ) * (1 - alphaSqrtTwoMO * (Real.sqrt 2 : ℂ))) + 1
          = 1 - (starRingEnd ℂ) alphaSqrtTwoMO * (Real.sqrt 2 : ℂ) +
              (starRingEnd ℂ) alphaSqrtTwoMO * alphaSqrtTwoMO *
                ((Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ)) := by ring
      _ = 1 - (starRingEnd ℂ) alphaSqrtTwoMO * (Real.sqrt 2 : ℂ) +
            (starRingEnd ℂ) alphaSqrtTwoMO * alphaSqrtTwoMO * 2 := by rw [hmul]
      _ = 1 - (starRingEnd ℂ) alphaSqrtTwoMO * (Real.sqrt 2 : ℂ) +
            (2 : ℂ) * (starRingEnd ℂ) alphaSqrtTwoMO * alphaSqrtTwoMO := by ring
  · simp [A3Shifted, K3, CrabbMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      Matrix.conjTranspose_apply, crabbWeight, smul_eq_mul]

lemma A3AdjALin_xWitness_eq_shiftedLinComb :
    A3AdjALin xWitness = shiftedLinComb xWitness dAstarAWitness := by
  have hAdjAE :
      A3AdjALin xWitness =
        WithLp.toLp (p := 2)
          ![(1 : ℂ) - alphaSqrtTwoMO * (Real.sqrt 2 : ℂ),
            (1 : ℂ) - star alphaSqrtTwoMO * (Real.sqrt 2 : ℂ) +
              (2 : ℂ) * star alphaSqrtTwoMO * alphaSqrtTwoMO,
            -(star alphaSqrtTwoMO * (Real.sqrt 2 : ℂ))] := by
    ext i
    simpa using congr_fun A3AdjALin_xWitness i
  have hAxE :
      A3Lin xWitness =
        WithLp.toLp (p := 2) ![(1 : ℂ) - alphaSqrtTwoMO * (Real.sqrt 2 : ℂ), 1, 0] := by
    ext i
    simpa using congr_fun A3Lin_xWitness i
  have hAadjE :
      A3AdjLin xWitness =
        WithLp.toLp (p := 2)
          ![(1 : ℂ), (1 : ℂ) - star alphaSqrtTwoMO * (Real.sqrt 2 : ℂ),
            -(star alphaSqrtTwoMO * (Real.sqrt 2 : ℂ))] := by
    ext i
    simpa using congr_fun A3AdjLin_xWitness i
  have hsq2 : ((Real.sqrt 2 : ℂ) ^ 2) = (2 : ℂ) := by
    have hsqR : (Real.sqrt 2) ^ 2 = 2 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by positivity)]
    exact_mod_cast hsqR
  have hsq3 : ((Real.sqrt 2 : ℂ) ^ 3) = (2 : ℂ) * (Real.sqrt 2 : ℂ) := by
    calc
      ((Real.sqrt 2 : ℂ) ^ 3) = ((Real.sqrt 2 : ℂ) ^ 2) * (Real.sqrt 2 : ℂ) := by ring
      _ = (2 : ℂ) * (Real.sqrt 2 : ℂ) := by rw [hsq2]
  have hsq4 : ((Real.sqrt 2 : ℂ) ^ 4) = (4 : ℂ) := by
    calc
      ((Real.sqrt 2 : ℂ) ^ 4) = (((Real.sqrt 2 : ℂ) ^ 2) ^ 2) := by ring
      _ = ((2 : ℂ) ^ 2) := by rw [hsq2]
      _ = (4 : ℂ) := by norm_num
  rw [hAdjAE, shiftedLinComb, dAstarAWitness, hAxE, hAadjE]
  ext i
  fin_cases i
  · simp [xWitness, alphaSqrtTwoMO, smul_eq_mul]
    ring_nf
    rw [hsq3, hsq4, hsq2]
    ring
  · simp [xWitness, alphaSqrtTwoMO, smul_eq_mul]
    ring
  · simp [xWitness, alphaSqrtTwoMO, smul_eq_mul]

/-- `xWitness` satisfies the generic quadratic decomposition hypotheses. -/
def hasShiftedQuadDecomp_xWitness : HasShiftedQuadDecomp xWitness where
  hA2_mem := by
    rw [A3SqLin_xWitness_eq_shiftedLinComb]
    exact shiftedLinComb_mem_shiftedSpan3 xWitness dA2Witness
  hAstarA_mem := by
    rw [A3AdjALin_xWitness_eq_shiftedLinComb]
    exact shiftedLinComb_mem_shiftedSpan3 xWitness dAstarAWitness

/-- Unconditional raw quadratic membership for the concrete witness vector. -/
theorem w_MO3_raw_quad_mem_shiftedSpan3_xWitness (raw : MO3RawQuadCoeffs) :
    w_MO3_raw_quad xWitness raw ∈ shiftedSpan3 xWitness :=
  w_MO3_raw_quad_mem_shiftedSpan3 xWitness raw hasShiftedQuadDecomp_xWitness

lemma A3Adj_witness_not_mem_span_x_A3x :
    A3AdjLin xWitness ∉ Submodule.span ℂ ({xWitness, A3Lin xWitness} : Set E3MO) := by
  intro hmem
  rcases (Submodule.mem_span_pair.mp hmem) with ⟨a, b, hab⟩
  have h2 : (a • xWitness + b • A3Lin xWitness).ofLp 2 = (A3AdjLin xWitness).ofLp 2 := by
    exact congrArg (fun v : E3MO => v.ofLp 2) hab
  have hA3lin2 : (A3Lin xWitness).ofLp 2 = 0 := by
    simpa using congr_fun A3Lin_xWitness 2
  have hA3adj2 :
      (A3AdjLin xWitness).ofLp 2 = -(star alphaSqrtTwoMO * (Real.sqrt 2 : ℂ)) := by
    simpa using congr_fun A3AdjLin_xWitness 2
  have h2' : a * (xWitness.ofLp 2) + b * (A3Lin xWitness).ofLp 2 = (A3AdjLin xWitness).ofLp 2 := by
    simpa [Pi.add_apply, smul_eq_mul] using h2
  have hsqrtR : (0 : ℝ) < Real.sqrt 2 := by positivity
  have hsqrt : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hsqrtR)
  have hαstar : star alphaSqrtTwoMO ≠ 0 := star_alphaSqrtTwoMO_ne_zero
  have hprod : star alphaSqrtTwoMO * (Real.sqrt 2 : ℂ) ≠ 0 := mul_ne_zero hαstar hsqrt
  have hx2 : xWitness.ofLp 2 = 0 := by simp [xWitness]
  rw [hx2, hA3lin2, hA3adj2] at h2'
  have h2'' : 0 = -(star alphaSqrtTwoMO * (Real.sqrt 2 : ℂ)) := by
    simpa using h2'
  have hzero : star alphaSqrtTwoMO * (Real.sqrt 2 : ℂ) = 0 := by
    exact neg_eq_zero.mp h2''.symm
  exact hprod hzero

/-- Concrete non-Hermitian `N=3` checkpoint for the shifted Crabb test case. -/
theorem mo3_nonhermitian_witness_package :
    ¬ A3Shifted.IsHermitian ∧
      shiftedSpan3 xWitness = moSpan3 xWitness ∧
      K3AdjLin xWitness ∉ Submodule.span ℂ ({xWitness, K3Lin xWitness} : Set E3MO) ∧
      A3AdjLin xWitness ∉ Submodule.span ℂ ({xWitness, A3Lin xWitness} : Set E3MO) := by
  refine ⟨A3Shifted_not_hermitian, shiftedSpan3_eq_moSpan3 xWitness, ?_, ?_⟩
  · exact k3Adj_witness_not_mem_span_x_k3x
  · exact A3Adj_witness_not_mem_span_x_A3x

end MyProject
