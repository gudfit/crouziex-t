import MyProject.MO3NonHermitian

noncomputable section

namespace MyProject

/-- Ambient space for the `N=4` non-Hermitian test block. -/
abbrev E4MO := EuclideanSpace ℂ (Fin 4)

/-- The `4×4` Crabb matrix. -/
abbrev K4 : Matrix (Fin 4) (Fin 4) ℂ := CrabbMatrix 4

/-- Shifted/scaled `4×4` test matrix `I - αK_4` with `α = 1 + √2`. -/
abbrev A4Shifted : Matrix (Fin 4) (Fin 4) ℂ :=
  (1 : Matrix (Fin 4) (Fin 4) ℂ) - alphaSqrtTwoMO • K4

/-- Linear action of `A4Shifted`. -/
abbrev A4Lin : E4MO →ₗ[ℂ] E4MO := Matrix.toEuclideanLin A4Shifted

/-- Linear action of `A4Shiftedᴴ`. -/
abbrev A4AdjLin : E4MO →ₗ[ℂ] E4MO := Matrix.toEuclideanLin A4Shifted.conjTranspose

/-- `N=4` shifted span `span{x, Ax, A* x}`. -/
def shiftedSpan4 (x : E4MO) : Submodule ℂ E4MO :=
  Submodule.span ℂ ({x, A4Lin x, A4AdjLin x} : Set E4MO)

/-- `A^2` action for the shifted `N=4` test matrix. -/
def A4SqLin (x : E4MO) : E4MO := A4Lin (A4Lin x)

/-- `N=4` witness vector. -/
def xBad4 : E4MO := WithLp.toLp (p := 2) ![(0 : ℂ), 0, 0, 1]

lemma A4Lin_xBad4 :
    A4Lin xBad4 = ![(0 : ℂ), 0, -(alphaSqrtTwoMO * (Real.sqrt 2 : ℂ)), 1] := by
  ext i
  fin_cases i <;>
    simp [A4Lin, A4Shifted, K4, xBad4, alphaSqrtTwoMO, CrabbMatrix, crabbWeight,
      Matrix.mulVec, dotProduct, Fin.sum_univ_four]

lemma A4AdjLin_xBad4 :
    A4AdjLin xBad4 = ![(0 : ℂ), 0, 0, 1] := by
  ext i
  fin_cases i <;>
    simp [A4AdjLin, A4Shifted, K4, xBad4, alphaSqrtTwoMO, CrabbMatrix, crabbWeight,
      Matrix.mulVec, dotProduct, Fin.sum_univ_four, Matrix.conjTranspose_apply]

lemma A4SqLin_xBad4 :
    A4SqLin xBad4 =
      ![(0 : ℂ), alphaSqrtTwoMO ^ 2 * (Real.sqrt 2 : ℂ),
        -(2 : ℂ) * alphaSqrtTwoMO * (Real.sqrt 2 : ℂ), 1] := by
  rw [A4SqLin, A4Lin, matrix_toEuclideanLin_apply, A4Lin_xBad4]
  ext i
  fin_cases i <;>
    simp [A4Shifted, K4, CrabbMatrix, crabbWeight, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four, smul_eq_mul]
    <;> ring

def secondCoordZeroSubmodule4 : Submodule ℂ E4MO where
  carrier := {y | y.ofLp 1 = 0}
  zero_mem' := by simp
  add_mem' := by
    intro y z hy hz
    have hy' : y.ofLp 1 = 0 := by simpa using hy
    have hz' : z.ofLp 1 = 0 := by simpa using hz
    calc
      (y + z).ofLp 1 = y.ofLp 1 + z.ofLp 1 := by simp
      _ = 0 := by simp [hy', hz']
  smul_mem' := by
    intro a y hy
    have hy' : y.ofLp 1 = 0 := by simpa using hy
    simp [hy']

lemma shiftedSpan4_xBad4_le_secondCoordZero : shiftedSpan4 xBad4 ≤ secondCoordZeroSubmodule4 := by
  refine Submodule.span_le.mpr ?_
  intro y hy
  change y.ofLp 1 = 0
  have hy' : y = xBad4 ∨ y = A4Lin xBad4 ∨ y = A4AdjLin xBad4 := by
    simpa [shiftedSpan4, Set.mem_insert_iff] using hy
  rcases hy' with rfl | hy''
  · simp [xBad4]
  · rcases hy'' with rfl | rfl
    · have h1 : (A4Lin xBad4).ofLp 1 = 0 := by
        simpa using congr_fun A4Lin_xBad4 1
      exact h1
    · have h1 : (A4AdjLin xBad4).ofLp 1 = 0 := by
        simpa using congr_fun A4AdjLin_xBad4 1
      exact h1

lemma shiftedSpan4_xBad4_second_zero (y : E4MO) (hy : y ∈ shiftedSpan4 xBad4) :
    y.ofLp 1 = 0 := by
  exact shiftedSpan4_xBad4_le_secondCoordZero hy

lemma A4SqLin_xBad4_second_ne_zero : (A4SqLin xBad4).ofLp 1 ≠ 0 := by
  have h1 : (A4SqLin xBad4).ofLp 1 = alphaSqrtTwoMO ^ 2 * (Real.sqrt 2 : ℂ) := by
    simpa using congr_fun A4SqLin_xBad4 1
  rw [h1]
  have hpow : alphaSqrtTwoMO ^ 2 ≠ 0 := pow_ne_zero 2 alphaSqrtTwoMO_ne_zero
  have hsqrtR : (0 : ℝ) < Real.sqrt 2 := by positivity
  have hsqrt : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hsqrtR)
  exact mul_ne_zero hpow hsqrt

lemma A4SqLin_xBad4_not_mem_shiftedSpan4 : A4SqLin xBad4 ∉ shiftedSpan4 xBad4 := by
  intro hmem
  have hzero : (A4SqLin xBad4).ofLp 1 = 0 := shiftedSpan4_xBad4_second_zero (A4SqLin xBad4) hmem
  exact A4SqLin_xBad4_second_ne_zero hzero

/--
`N=4` analogue of the `N=3` pointwise-failure phenomenon:
the universal pointwise claim `A^2x ∈ span{x,Ax,A* x}` fails.
-/
theorem not_forall_A4SqLin_mem_shiftedSpan4 : ¬ (∀ x : E4MO, A4SqLin x ∈ shiftedSpan4 x) := by
  intro hAll
  exact A4SqLin_xBad4_not_mem_shiftedSpan4 (hAll xBad4)

theorem exists_A4SqLin_not_mem_shiftedSpan4 : ∃ x : E4MO, A4SqLin x ∉ shiftedSpan4 x :=
  ⟨xBad4, A4SqLin_xBad4_not_mem_shiftedSpan4⟩

/-- Orthogonal-direction witness used for the exact `d=3` multilinear MO expression. -/
def xiBad4 : E4MO := WithLp.toLp (p := 2) ![(0 : ℂ), 1, 0, 0]

lemma inner_eq_star_second_xiBad4 (y : E4MO) :
    inner ℂ y xiBad4 = star (y.ofLp 1) := by
  simp [xiBad4, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_four]

lemma inner_xiBad4_eq_second (y : E4MO) :
    inner ℂ xiBad4 y = y.ofLp 1 := by
  simp [xiBad4, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_four]

lemma xiBad4_mem_orthogonal_shiftedSpan4_xBad4 : xiBad4 ∈ (shiftedSpan4 xBad4)ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro y hy
  have hy1 : y.ofLp 1 = 0 := shiftedSpan4_xBad4_second_zero y hy
  rw [inner_eq_star_second_xiBad4]
  simp [hy1]

lemma inner_xiBad4_xBad4 : inner ℂ xiBad4 xBad4 = 0 := by
  simp [inner_xiBad4_eq_second, xBad4]

lemma inner_xBad4_xiBad4 : inner ℂ xBad4 xiBad4 = 0 := by
  simp [xBad4, xiBad4, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_four]

lemma inner_xiBad4_A4Lin_xBad4 : inner ℂ xiBad4 (A4Lin xBad4) = 0 := by
  simp [inner_xiBad4_eq_second, A4Lin, A4Shifted, K4, xBad4, alphaSqrtTwoMO, CrabbMatrix,
    crabbWeight, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

lemma inner_xiBad4_A4SqLin_xBad4 :
    inner ℂ xiBad4 (A4SqLin xBad4) = alphaSqrtTwoMO ^ 2 * (Real.sqrt 2 : ℂ) := by
  simpa [inner_xiBad4_eq_second] using congr_fun A4SqLin_xBad4 1

lemma inner_A4AdjLin_xBad4_xiBad4 : inner ℂ (A4AdjLin xBad4) xiBad4 = 0 := by
  have h1 : (A4AdjLin xBad4).ofLp 1 = 0 := by
    simpa using congr_fun A4AdjLin_xBad4 1
  rw [inner_eq_star_second_xiBad4]
  simp [h1]

/-- Iterated action of `A4Lin`. -/
def A4PowAct : ℕ → E4MO → E4MO
  | 0, x => x
  | n + 1, x => A4Lin (A4PowAct n x)

/-- Iterated action of `A4AdjLin`. -/
def A4AdjPowAct : ℕ → E4MO → E4MO
  | 0, x => x
  | n + 1, x => A4AdjLin (A4AdjPowAct n x)

lemma A4PowAct_two (x : E4MO) : A4PowAct 2 x = A4SqLin x := rfl

lemma A4AdjPowAct_two_xBad4 : A4AdjPowAct 2 xBad4 = xBad4 := by
  have hx : A4AdjLin xBad4 = xBad4 := by
    simpa [xBad4] using A4AdjLin_xBad4
  simp [A4AdjPowAct, hx]

lemma inner_A4AdjPowAct_two_xBad4_xiBad4 : inner ℂ (A4AdjPowAct 2 xBad4) xiBad4 = 0 := by
  rw [A4AdjPowAct_two_xBad4]
  exact inner_xBad4_xiBad4

/-- `a_m` lookup for degree-`3` coefficient packages (`a_0,...,a_3`), zero above degree. -/
def coeffAt4 (a : Fin 4 → ℂ) (m : ℕ) : ℂ :=
  if h : m < 4 then a ⟨m, h⟩ else 0

/-- Exact `c_{jk}` map used by the truncated resolvent expansion at degree `3`. -/
def cjkFromCoeff4 (a : Fin 4 → ℂ) (j k : Fin 3) : ℂ :=
  coeffAt4 a (j.1 + k.1 + 1)

/--
Degree-`3` multilinear first-variation expression from the expanded open-lemma formula.
This is the exact `c_{jk}`-weighted object (no symbolic raw compression).
-/
def mo4MultilinearD3 (x v ξ : E4MO) (cjk : Fin 3 → Fin 3 → ℂ) : ℂ :=
  ∑ j, ∑ k,
    (cjk j k * (inner ℂ x (A4PowAct j v)) * (inner ℂ ξ (A4PowAct k x)) +
      star (cjk j k) * (inner ℂ (A4AdjPowAct k x) ξ) * (inner ℂ v (A4AdjPowAct j x)))

/-- Degree-`3` multilinear first variation built from a coefficient package `a_0,...,a_3`. -/
def mo4MultilinearD3Exact (x v ξ : E4MO) (a : Fin 4 → ℂ) : ℂ :=
  mo4MultilinearD3 x v ξ (cjkFromCoeff4 a)

/-- Naive unconditional exact-`d=3` MO claim for a fixed coefficient package. -/
def MO4D3ExactUnconditional (a : Fin 4 → ℂ) : Prop :=
  ∀ x v ξ, ξ ∈ (shiftedSpan4 x)ᗮ → inner ℂ ξ v = 0 →
    Complex.re (mo4MultilinearD3Exact x v ξ a) = 0

/--
Cubic setup under which the exact multilinear `d=3` first variation vanishes:
orthogonality plus decomposition of `A^2x` and `(A^*)^2 x` into `span{x,Ax,A* x}`.
-/
structure MO4CubicSetup (x ξ : E4MO) : Prop where
  h_ξ_orth : ξ ∈ (shiftedSpan4 x)ᗮ
  hA2_mem : A4PowAct 2 x ∈ shiftedSpan4 x
  hAstar2_mem : A4AdjPowAct 2 x ∈ shiftedSpan4 x

/--
Correct conditional form for exact `d=3` coefficients:
vanishing holds once the cubic decomposition assumptions are present.
-/
theorem mo4MultilinearD3Exact_re_zero_of_setup
    (x v ξ : E4MO) (a : Fin 4 → ℂ) (hsetup : MO4CubicSetup x ξ) :
    Complex.re (mo4MultilinearD3Exact x v ξ a) = 0 := by
  have horth : ∀ y ∈ shiftedSpan4 x, inner ℂ y ξ = 0 :=
    (Submodule.mem_orthogonal (shiftedSpan4 x) ξ).1 hsetup.h_ξ_orth
  have horthLeft : ∀ y ∈ shiftedSpan4 x, inner ℂ ξ y = 0 := by
    intro y hy
    exact (inner_eq_zero_symm).1 (horth y hy)
  have hx_mem : x ∈ shiftedSpan4 x := by
    exact Submodule.subset_span (by simp [Set.mem_insert_iff])
  have hAx_mem : A4Lin x ∈ shiftedSpan4 x := by
    exact Submodule.subset_span (by simp [Set.mem_insert_iff])
  have hAstarx_mem : A4AdjLin x ∈ shiftedSpan4 x := by
    exact Submodule.subset_span (by simp [Set.mem_insert_iff])
  have hPow0 : inner ℂ ξ (A4PowAct 0 x) = 0 := by
    simpa [A4PowAct] using horthLeft x hx_mem
  have hPow1 : inner ℂ ξ (A4PowAct 1 x) = 0 := by
    simpa [A4PowAct] using horthLeft (A4Lin x) hAx_mem
  have hPow2 : inner ℂ ξ (A4PowAct 2 x) = 0 :=
    horthLeft (A4PowAct 2 x) hsetup.hA2_mem
  have hAdj0 : inner ℂ (A4AdjPowAct 0 x) ξ = 0 := by
    simpa [A4AdjPowAct] using horth x hx_mem
  have hAdj1 : inner ℂ (A4AdjPowAct 1 x) ξ = 0 := by
    simpa [A4AdjPowAct] using horth (A4AdjLin x) hAstarx_mem
  have hAdj2 : inner ℂ (A4AdjPowAct 2 x) ξ = 0 :=
    horth (A4AdjPowAct 2 x) hsetup.hAstar2_mem
  have hzero : mo4MultilinearD3 x v ξ (cjkFromCoeff4 a) = 0 := by
    unfold mo4MultilinearD3
    refine Finset.sum_eq_zero ?_
    intro j hj
    refine Finset.sum_eq_zero ?_
    intro k hk
    fin_cases k
    · simp [hPow0, hAdj0]
    · simp [hPow1, hAdj1]
    · simp [hPow2, hAdj2]
  rw [mo4MultilinearD3Exact, hzero]
  simp

/-- Monomial coefficient package `f(z)=z^3`, so `a_3=1` and `a_0=a_1=a_2=0`. -/
def z3Coeffs4 : Fin 4 → ℂ := ![(0 : ℂ), 0, 0, 1]

/-- Expanded `d=3` expression specialized to `f(z)=z^3` (`c_{02}=c_{11}=c_{20}=1`). -/
def mo4MultilinearZ3 (x v ξ : E4MO) : ℂ :=
  (inner ℂ x v) * (inner ℂ ξ (A4PowAct 2 x)) +
    (inner ℂ x (A4Lin v)) * (inner ℂ ξ (A4Lin x)) +
    (inner ℂ x (A4PowAct 2 v)) * (inner ℂ ξ x) +
    (inner ℂ (A4AdjPowAct 2 x) ξ) * (inner ℂ v x) +
    (inner ℂ (A4AdjLin x) ξ) * (inner ℂ v (A4AdjLin x)) +
    (inner ℂ x ξ) * (inner ℂ v (A4AdjPowAct 2 x))

lemma mo4MultilinearD3Exact_z3_eq (x v ξ : E4MO) :
    mo4MultilinearD3Exact x v ξ z3Coeffs4 = mo4MultilinearZ3 x v ξ := by
  unfold mo4MultilinearD3Exact mo4MultilinearD3 mo4MultilinearZ3
    cjkFromCoeff4 coeffAt4 z3Coeffs4
  simp [Fin.sum_univ_three, A4PowAct, A4AdjPowAct]
  ring

lemma inner_xBad4_xBad4 : inner ℂ xBad4 xBad4 = (1 : ℂ) := by
  have hnormsq : ‖xBad4‖ ^ 2 = (1 : ℝ) := by
    rw [norm_sq_eq_sum_abs_sq]
    simp [xBad4, Fin.sum_univ_four]
  rw [inner_self_eq_norm_sq_to_K]
  have hcast : ((‖xBad4‖ ^ 2 : ℝ) : ℂ) = (1 : ℂ) :=
    congrArg (fun t : ℝ => (t : ℂ)) hnormsq
  simpa [pow_two] using hcast

lemma mo4MultilinearZ3_xBad4_xBad4_xiBad4 :
    mo4MultilinearZ3 xBad4 xBad4 xiBad4 = alphaSqrtTwoMO ^ 2 * (Real.sqrt 2 : ℂ) := by
  unfold mo4MultilinearZ3
  have hξx : inner ℂ xiBad4 xBad4 = 0 := inner_xiBad4_xBad4
  have hξAx : inner ℂ xiBad4 (A4Lin xBad4) = 0 := inner_xiBad4_A4Lin_xBad4
  have hξA2x : inner ℂ xiBad4 (A4PowAct 2 xBad4) = alphaSqrtTwoMO ^ 2 * (Real.sqrt 2 : ℂ) := by
    simpa [A4PowAct_two] using inner_xiBad4_A4SqLin_xBad4
  have hAstar2 : inner ℂ (A4AdjPowAct 2 xBad4) xiBad4 = 0 := inner_A4AdjPowAct_two_xBad4_xiBad4
  have hAstar1 : inner ℂ (A4AdjLin xBad4) xiBad4 = 0 := inner_A4AdjLin_xBad4_xiBad4
  have hxξ : inner ℂ xBad4 xiBad4 = 0 := inner_xBad4_xiBad4
  have hxx : inner ℂ xBad4 xBad4 = (1 : ℂ) := inner_xBad4_xBad4
  rw [hξA2x, hξAx, hξx, hAstar2, hAstar1, hxξ, hxx]
  simp

lemma mo4MultilinearZ3_xBad4_xBad4_xiBad4_re_pos :
    0 < Complex.re (mo4MultilinearZ3 xBad4 xBad4 xiBad4) := by
  rw [mo4MultilinearZ3_xBad4_xBad4_xiBad4]
  have hre : Complex.re (alphaSqrtTwoMO ^ 2 * (Real.sqrt 2 : ℂ)) = (1 + Real.sqrt 2) ^ 2 * Real.sqrt 2 := by
    have hc : alphaSqrtTwoMO ^ 2 * (Real.sqrt 2 : ℂ) = (((1 + Real.sqrt 2) ^ 2 * Real.sqrt 2 : ℝ) : ℂ) := by
      simp [alphaSqrtTwoMO]
    rw [hc, Complex.ofReal_re]
  rw [hre]
  positivity

lemma mo4MultilinearD3Exact_z3_xBad4_xBad4_xiBad4_re_pos :
    0 < Complex.re (mo4MultilinearD3Exact xBad4 xBad4 xiBad4 z3Coeffs4) := by
  rw [mo4MultilinearD3Exact_z3_eq]
  exact mo4MultilinearZ3_xBad4_xBad4_xiBad4_re_pos

/--
For the explicit witness `xBad4, xiBad4`, the exact multilinear `d=3` expression
with `v = conj(a_3) • xBad4` collapses to a positive scalar multiple of `a_3 * conj(a_3)`.
-/
lemma mo4MultilinearD3Exact_xBad4_scaled_xiBad4 (a : Fin 4 → ℂ) :
    mo4MultilinearD3Exact xBad4 (star (a 3) • xBad4) xiBad4 a =
      a 3 * star (a 3) * (alphaSqrtTwoMO ^ 2 * (Real.sqrt 2 : ℂ)) := by
  have hPow0 : inner ℂ xiBad4 (A4PowAct 0 xBad4) = 0 := by
    simpa [A4PowAct] using inner_xiBad4_xBad4
  have hPow1 : inner ℂ xiBad4 (A4PowAct 1 xBad4) = 0 := by
    simpa [A4PowAct] using inner_xiBad4_A4Lin_xBad4
  have hPow2 :
      inner ℂ xiBad4 (A4PowAct 2 xBad4) = alphaSqrtTwoMO ^ 2 * (Real.sqrt 2 : ℂ) := by
    simpa [A4PowAct_two] using inner_xiBad4_A4SqLin_xBad4
  have hAdj0 : inner ℂ (A4AdjPowAct 0 xBad4) xiBad4 = 0 := by
    simpa [A4AdjPowAct] using inner_xBad4_xiBad4
  have hAdj1 : inner ℂ (A4AdjPowAct 1 xBad4) xiBad4 = 0 := by
    simpa [A4AdjPowAct] using inner_A4AdjLin_xBad4_xiBad4
  rw [mo4MultilinearD3Exact, mo4MultilinearD3]
  simp [Fin.sum_univ_three, cjkFromCoeff4, coeffAt4, hPow0, hPow1, hPow2, hAdj0, hAdj1,
    A4AdjPowAct_two_xBad4]
  have hnormsq : ‖xBad4‖ ^ 2 = (1 : ℝ) := by
    rw [norm_sq_eq_sum_abs_sq]
    simp [xBad4, Fin.sum_univ_four]
  have hnormC : ((‖xBad4‖ : ℂ) ^ 2) = (1 : ℂ) := by
    exact_mod_cast hnormsq
  have hxv : inner ℂ xBad4 (A4PowAct 0 (star (a 3) • xBad4)) = star (a 3) := by
    simp [A4PowAct, hnormC]
  have hxv' :
      inner ℂ xBad4 (A4PowAct 0 ((starRingEnd ℂ) (a 3) • xBad4)) = (starRingEnd ℂ) (a 3) := by
    simpa using hxv
  rw [hxv', inner_xBad4_xiBad4]
  ring

lemma mo4MultilinearD3Exact_xBad4_scaled_xiBad4_re_pos_of_topCoeff_ne_zero
    (a : Fin 4 → ℂ) (ha3 : a 3 ≠ 0) :
    0 < Complex.re (mo4MultilinearD3Exact xBad4 (star (a 3) • xBad4) xiBad4 a) := by
  rw [mo4MultilinearD3Exact_xBad4_scaled_xiBad4]
  have hconj : a 3 * star (a 3) = (Complex.normSq (a 3) : ℂ) := by
    simpa using Complex.mul_conj (a 3)
  rw [hconj]
  have ht : alphaSqrtTwoMO ^ 2 * (Real.sqrt 2 : ℂ) =
      (((1 + Real.sqrt 2) ^ 2 * Real.sqrt 2 : ℝ) : ℂ) := by
    simp [alphaSqrtTwoMO]
  rw [ht]
  have hrealmul :
      ((Complex.normSq (a 3) : ℂ) * (((1 + Real.sqrt 2) ^ 2 * Real.sqrt 2 : ℝ) : ℂ)) =
        (((Complex.normSq (a 3) * ((1 + Real.sqrt 2) ^ 2 * Real.sqrt 2) : ℝ)) : ℂ) := by
    norm_num [Complex.normSq, Complex.ofReal_re, Complex.ofReal_im]
  rw [hrealmul, Complex.ofReal_re]
  have hnorm_pos : 0 < Complex.normSq (a 3) := (Complex.normSq_pos).2 ha3
  have ht_pos : 0 < ((1 + Real.sqrt 2) ^ 2 * Real.sqrt 2 : ℝ) := by
    positivity
  exact mul_pos hnorm_pos ht_pos

theorem not_unconditional_mo4_d3_exact_of_topCoeff_ne_zero
    (a : Fin 4 → ℂ) (ha3 : a 3 ≠ 0) :
    ¬ MO4D3ExactUnconditional a := by
  intro h
  let vBad : E4MO := star (a 3) • xBad4
  have hvBad_orth : inner ℂ xiBad4 vBad = 0 := by
    simp [vBad, inner_xiBad4_xBad4]
  have hzero : Complex.re (mo4MultilinearD3Exact xBad4 vBad xiBad4 a) = 0 :=
    h xBad4 vBad xiBad4 xiBad4_mem_orthogonal_shiftedSpan4_xBad4 hvBad_orth
  have hpos : 0 < Complex.re (mo4MultilinearD3Exact xBad4 vBad xiBad4 a) := by
    simpa [vBad] using
      mo4MultilinearD3Exact_xBad4_scaled_xiBad4_re_pos_of_topCoeff_ne_zero a ha3
  exact (ne_of_gt hpos) hzero

theorem exists_mo4_d3_exact_counterexample_of_topCoeff_ne_zero
    (a : Fin 4 → ℂ) (ha3 : a 3 ≠ 0) :
    ∃ x v ξ, ξ ∈ (shiftedSpan4 x)ᗮ ∧ inner ℂ ξ v = 0 ∧
      Complex.re (mo4MultilinearD3Exact x v ξ a) ≠ 0 := by
  refine ⟨xBad4, star (a 3) • xBad4, xiBad4, xiBad4_mem_orthogonal_shiftedSpan4_xBad4, ?_, ?_⟩
  · simp [inner_xiBad4_xBad4]
  · exact ne_of_gt
      (mo4MultilinearD3Exact_xBad4_scaled_xiBad4_re_pos_of_topCoeff_ne_zero a ha3)

theorem not_forall_coeffs_unconditional_mo4_d3_exact :
    ¬ (∀ a : Fin 4 → ℂ, MO4D3ExactUnconditional a) := by
  intro hAll
  have hz3 : z3Coeffs4 3 ≠ 0 := by simp [z3Coeffs4]
  exact not_unconditional_mo4_d3_exact_of_topCoeff_ne_zero z3Coeffs4 hz3 (hAll z3Coeffs4)

/--
Exact-coefficient (`c_{jk}` from `a_{j+k+1}`) `d=3` unconditional MO claim is false
in the shifted `N=4` Crabb model, even with the normalization-direction constraint `ξ ⟂ v`.
-/
theorem not_unconditional_mo4_d3_exact_z3 :
    ¬ MO4D3ExactUnconditional z3Coeffs4 := by
  intro h
  have hzero : Complex.re (mo4MultilinearD3Exact xBad4 xBad4 xiBad4 z3Coeffs4) = 0 :=
    h xBad4 xBad4 xiBad4 xiBad4_mem_orthogonal_shiftedSpan4_xBad4 inner_xiBad4_xBad4
  exact (ne_of_gt mo4MultilinearD3Exact_z3_xBad4_xBad4_xiBad4_re_pos) hzero

theorem exists_mo4_d3_exact_z3_counterexample :
    ∃ x v ξ, ξ ∈ (shiftedSpan4 x)ᗮ ∧ inner ℂ ξ v = 0 ∧
      Complex.re (mo4MultilinearD3Exact x v ξ z3Coeffs4) ≠ 0 := by
  refine ⟨xBad4, xBad4, xiBad4, xiBad4_mem_orthogonal_shiftedSpan4_xBad4, inner_xiBad4_xBad4, ?_⟩
  exact ne_of_gt mo4MultilinearD3Exact_z3_xBad4_xBad4_xiBad4_re_pos

end MyProject
