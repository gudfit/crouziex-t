import Mathlib

open scoped ComplexInnerProductSpace
open Metric
open Set
open LinearMap
open Matrix
open Complex
open Basis
open Module
open FiniteDimensional


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def numericalRange (A : E →L[ℂ] E) : Set ℂ :=
  { z | ∃ x : E, ‖x‖ = 1 ∧ z = ⟪A x, x⟫ }

lemma mem_numericalRange_of_unit {A : E →L[ℂ] E} {x : E}
    (hx : ‖x‖ = 1) :
    ⟪A x, x⟫ ∈ numericalRange A := by
  refine ⟨x, hx, rfl⟩

lemma norm_le_opNorm_of_mem_numericalRange
    {A : E →L[ℂ] E} {z : ℂ}
    (hz : z ∈ numericalRange A) :
    ‖z‖ ≤ ‖A‖ := by
  rcases hz with ⟨x, hx, rfl⟩
  have hx0 : 0 ≤ ‖x‖ := norm_nonneg x
  calc
    ‖⟪A x, x⟫‖ ≤ ‖A x‖ * ‖x‖ := norm_inner_le_norm (A x) x
    _ ≤ ‖A‖ * ‖x‖ * ‖x‖ := by
      have h := mul_le_mul_of_nonneg_right (A.le_opNorm x) hx0
      simpa [mul_comm, mul_left_comm, mul_assoc] using h
    _ ≤ ‖A‖ := by
      simp [hx]

lemma numericalRange_subset_closedBall (A : E →L[ℂ] E) :
    numericalRange A ⊆ closedBall (0 : ℂ) ‖A‖ := by
  intro z hz
  have hz' : ‖z‖ ≤ ‖A‖ :=
    norm_le_opNorm_of_mem_numericalRange (A := A) hz
  simpa [closedBall, dist_eq_norm] using hz'

def DWShell (A : E →L[ℂ] E) : Set (ℂ × ℝ) :=
  { p | ∃ x : E, ‖x‖ = 1 ∧ p.1 = ⟪A x, x⟫ ∧ p.2 = ‖A x‖^2 }

lemma mem_DWShell_of_unit {A : E →L[ℂ] E} {x : E}
    (hx : ‖x‖ = 1) :
    (⟪A x, x⟫, ‖A x‖^2) ∈ DWShell A := by
  refine ⟨x, hx, ?_, ?_⟩
  · rfl
  · rfl

lemma fst_image_DWShell (A : E →L[ℂ] E) :
    Prod.fst '' DWShell A = numericalRange A := by
  ext z
  constructor
  · intro hz
    rcases hz with ⟨p, hp, rfl⟩
    rcases hp with ⟨x, hx, hpx, hp2⟩
    exact ⟨x, hx, hpx⟩
  · intro hz
    rcases hz with ⟨x, hx, rfl⟩
    refine ⟨(⟪A x, x⟫, ‖A x‖^2), ?_, rfl⟩
    exact mem_DWShell_of_unit (A := A) hx

lemma DWShell_subset_productBall (A : E →L[ℂ] E) :
    DWShell A ⊆ (closedBall (0 : ℂ) ‖A‖) ×ˢ Set.Icc (0 : ℝ) (‖A‖^2) := by
  intro p hp
  rcases hp with ⟨x, hx, h₁, h₂⟩
  have hz : ‖⟪A x, x⟫‖ ≤ ‖A‖ :=
    norm_le_opNorm_of_mem_numericalRange
      (A := A) (z := ⟪A x, x⟫) ⟨x, hx, rfl⟩
  have hAx : ‖A x‖ ≤ ‖A‖ * ‖x‖ := A.le_opNorm x
  have hAx' : ‖A x‖ ≤ ‖A‖ := by simpa [hx, one_mul] using hAx
  have h2' : ‖A x‖^2 ≤ ‖A‖^2 := by
    have h' : |‖A x‖| ≤ |‖A‖| := by
      simpa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] using hAx'
    exact (sq_le_sq.mpr h')
  refine ⟨?_, ?_⟩
  · have hz' : ‖p.1‖ ≤ ‖A‖ := by
      simpa [h₁] using hz
    simpa [closedBall, dist_eq_norm] using hz'
  · have h0 : 0 ≤ p.2 := by
      have : 0 ≤ ‖A x‖^2 := sq_nonneg _
      simp [h₂]
    have hle : p.2 ≤ ‖A‖^2 := by
      have : ‖A x‖^2 ≤ ‖A‖^2 := h2'
      simpa [h₂] using this
    exact ⟨h0, hle⟩

section GeometricProperties
variable {A : E →L[ℂ] E}

lemma dw_shell_paraboloid_property {p : ℂ × ℝ} (hp : p ∈ DWShell A) :
    ‖p.1‖ ^ 2 ≤ p.2 := by
  rcases hp with ⟨x, hx, h1, h2⟩
  rw [h1, h2]
  apply sq_le_sq.mpr
  rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)]
  have h_cs := norm_inner_le_norm (𝕜 := ℂ) (A x) x
  rw [hx, mul_one] at h_cs
  exact h_cs

noncomputable def numericalRadius (A : E →L[ℂ] E) : ℝ :=
  sSup { r | ∃ z ∈ numericalRange A, r = ‖z‖ }

lemma numericalRadius_le_opNorm (A : E →L[ℂ] E) :
    numericalRadius A ≤ ‖A‖ := by
  apply Real.sSup_le
  · intro r hr
    rcases hr with ⟨z, hz, rfl⟩
    exact norm_le_opNorm_of_mem_numericalRange hz
  · exact norm_nonneg A

end GeometricProperties

section UnitaryInvariance
variable (U : E ≃ₗᵢ[ℂ] E)
variable (A : E →L[ℂ] E)

def unitary_conjugate : E →L[ℂ] E :=
  (U.symm : E →L[ℂ] E).comp (A.comp (U : E →L[ℂ] E))

lemma unitary_map_sphere (x : E) :
    ‖U x‖ = 1 ↔ ‖x‖ = 1 := by
  simp only [LinearIsometryEquiv.norm_map]

lemma unitary_conjugate_inner (x : E) :
    ⟪unitary_conjugate U A x, x⟫ = ⟪A (U x), U x⟫ := by
  simp only [unitary_conjugate, ContinuousLinearMap.comp_apply]
  rw [← U.inner_map_map]
  simp

lemma unitary_conjugate_norm_sq (x : E) :
    ‖unitary_conjugate U A x‖^2 = ‖A (U x)‖^2 := by
  simp only [unitary_conjugate, ContinuousLinearMap.comp_apply]
  simp

lemma dw_shell_unitary_subset :
    DWShell (unitary_conjugate U A) ⊆ DWShell A := by
  intro p hp
  rcases hp with ⟨x, hx, h1, h2⟩
  use U x
  refine ⟨?_, ?_, ?_⟩
  · rwa [unitary_map_sphere]
  · rw [h1, unitary_conjugate_inner]
  · rw [h2, unitary_conjugate_norm_sq]

lemma dw_shell_subset_unitary :
    DWShell A ⊆ DWShell (unitary_conjugate U A) := by
  intro p hp
  rcases hp with ⟨x, hx, h1, h2⟩
  use U.symm x
  refine ⟨?_, ?_, ?_⟩
  · rw [LinearIsometryEquiv.norm_map]
    exact hx
  · rw [unitary_conjugate_inner, LinearIsometryEquiv.apply_symm_apply]
    exact h1
  · rw [unitary_conjugate_norm_sq, LinearIsometryEquiv.apply_symm_apply]
    exact h2

theorem dw_shell_unitary_invariant :
    DWShell (unitary_conjugate U A) = DWShell A :=
  Subset.antisymm (dw_shell_unitary_subset U A) (dw_shell_subset_unitary U A)

end UnitaryInvariance

section CrabbProperties
open scoped BigOperators

variable {n : ℕ}

noncomputable def crabbWeight (n : ℕ) (i : Fin (n - 1)) : ℂ :=
  (if i.val = 0 then (Real.sqrt 2 : ℂ) else 1) *
  (if i.val = n - 2 then (Real.sqrt 2 : ℂ) else 1)

noncomputable def CrabbMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j =>
    if h : j.val = i.val + 1 then
      have hi : i.val < n - 1 := by
        have h_lt := j.is_lt
        rw [h] at h_lt
        omega
      crabbWeight n ⟨i.val, hi⟩
    else
      0

lemma sqrt_two_mul_sqrt_two : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
  have h : (Real.sqrt 2 : ℝ)^2 = 2 := Real.sq_sqrt (by norm_num)
  rw [← ofReal_mul, ← pow_two, h]
  simp

lemma prod_crabbWeight_split :
    ∏ i : Fin (n - 1), crabbWeight n i =
    (∏ i : Fin (n - 1), (if i.val = 0 then (Real.sqrt 2 : ℂ) else 1)) *
    (∏ i : Fin (n - 1), (if i.val = n - 2 then (Real.sqrt 2 : ℂ) else 1)) := by
  simp only [crabbWeight, Finset.prod_mul_distrib]

lemma prod_ite_zero_eq_sqrt (hn : n ≥ 2) :
    ∏ i : Fin (n - 1), (if i.val = 0 then (Real.sqrt 2 : ℂ) else 1) = Real.sqrt 2 := by
  have h_idx : 0 < n - 1 := Nat.sub_pos_of_lt hn
  let i₀ : Fin (n - 1) := ⟨0, h_idx⟩
  apply Finset.prod_eq_single i₀
  · intro b _ hb
    rw [if_neg]
    intro h_eq
    apply hb
    apply Fin.ext
    exact h_eq
  · intro h_nin
    exfalso
    exact h_nin (Finset.mem_univ i₀)

lemma prod_ite_last_eq_sqrt (hn : n ≥ 2) :
    ∏ i : Fin (n - 1), (if i.val = n - 2 then (Real.sqrt 2 : ℂ) else 1) = Real.sqrt 2 := by
  have h_idx : n - 2 < n - 1 := Nat.sub_lt_sub_left hn (by norm_num)
  let i_last : Fin (n - 1) := ⟨n - 2, h_idx⟩
  convert Finset.prod_eq_single i_last _ _
  · simp [i_last]
  · intro b _ hb
    rw [if_neg]
    intro h_eq
    apply hb
    apply Fin.ext
    exact h_eq
  · intro h_nin
    exfalso
    exact h_nin (Finset.mem_univ i_last)

lemma crabb_weight_prod_eq_two (hn : n ≥ 2) :
    ∏ i : Fin (n - 1), crabbWeight n i = 2 := by
  rw [prod_crabbWeight_split]
  rw [prod_ite_zero_eq_sqrt hn]
  rw [prod_ite_last_eq_sqrt hn]
  exact sqrt_two_mul_sqrt_two

lemma sparsity_one (n : ℕ) :
    ∀ (i j : Fin n), (1 : Matrix (Fin n) (Fin n) ℂ) i j ≠ 0 → j.val = i.val + 0 := by
  intro i j h
  rw [Matrix.one_apply] at h
  split_ifs at h with heq
  · rw [heq, add_zero]
  · contradiction

lemma sparsity_mul {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (a b : ℕ)
    (hA : ∀ i j, A i j ≠ 0 → j.val = i.val + a)
    (hB : ∀ i j, B i j ≠ 0 → j.val = i.val + b) :
    ∀ i j, (A * B) i j ≠ 0 → j.val = i.val + a + b := by
  intro i k hik
  rw [Matrix.mul_apply] at hik
  have ⟨j, _, hj_prod⟩ := Finset.exists_ne_zero_of_sum_ne_zero hik
  have hA_nz : A i j ≠ 0 := left_ne_zero_of_mul hj_prod
  have hB_nz : B j k ≠ 0 := right_ne_zero_of_mul hj_prod
  rw [hB j k hB_nz]
  rw [hA i j hA_nz]

lemma superdiag_pow_sparsity (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, A i j ≠ 0 → j.val = i.val + 1) (k : ℕ) :
    ∀ i j, (A ^ k) i j ≠ 0 → j.val = i.val + k := by
  induction k with
  | zero =>
    rw [pow_zero]
    exact sparsity_one n
  | succ k ih =>
    rw [pow_succ]
    apply sparsity_mul (A^k) A k 1
    · exact ih
    · exact hA

lemma crabbMatrix_pow_n_eq_zero (n : ℕ) : CrabbMatrix n ^ n = 0 := by
  ext i j
  by_cases hzero : (CrabbMatrix n ^ n) i j = 0
  · exact hzero
  · exfalso
    have h_shift : j.val = i.val + n := by
      exact superdiag_pow_sparsity (n := n) (A := CrabbMatrix n)
        (hA := by
          intro i j h_nz
          classical
          by_contra h'
          have : CrabbMatrix n i j = 0 := by
            simp [CrabbMatrix, h']
          exact h_nz this) n i j hzero
    have h_ge : n ≤ j.val := by
      rw [h_shift]
      simp [Nat.add_comm]
    exact (Nat.not_lt_of_ge h_ge) j.is_lt

lemma crabb_entry_val {n : ℕ} (i j : Fin n) (h : j.val = i.val + 1) (hi : i.val < n - 1) :
    CrabbMatrix n i j = crabbWeight n ⟨i.val, hi⟩ := by
  classical
  simp [CrabbMatrix, h]

lemma mul_superdiag_entry (A : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) (k : ℕ)
    (hk : k < n - 1) :
    let j_curr : Fin n := ⟨k, by omega⟩
    let j_next : Fin n := ⟨k + 1, by omega⟩
    (A * CrabbMatrix n) i j_next = A i j_curr * CrabbMatrix n j_curr j_next := by
  intro j_curr j_next
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_single j_curr
  · intro x _ hx_ne
    unfold CrabbMatrix
    rw [dif_neg]
    · simp
    · intro h_shift
      apply hx_ne
      apply Fin.ext
      simp [j_next] at h_shift
      have : x.val = k := by omega
      simp [j_curr, this]
  · simp

lemma pow_recurrence (k : ℕ) (hk : k < n - 1) :
    (CrabbMatrix n ^ (k + 1)) ⟨0, by omega⟩ ⟨k + 1, by omega⟩ =
    (CrabbMatrix n ^ k) ⟨0, by omega⟩ ⟨k, by omega⟩ * crabbWeight n ⟨k, hk⟩ := by
  classical
  let i_zero : Fin n := ⟨0, by omega⟩
  let j_curr : Fin n := ⟨k, by omega⟩
  let j_next : Fin n := ⟨k + 1, by omega⟩
  have h_mul :
      (CrabbMatrix n ^ (k + 1)) i_zero j_next =
        (CrabbMatrix n ^ k) i_zero j_curr * CrabbMatrix n j_curr j_next := by
    have h :=
      mul_superdiag_entry (n := n) (A := CrabbMatrix n ^ k)
        (i := i_zero) (k := k) (hk := hk)
    simpa [i_zero, j_curr, j_next, pow_succ] using h
  have h_cond : j_next.val = j_curr.val + 1 := by
    simp [j_curr, j_next]
  calc
    (CrabbMatrix n ^ (k + 1)) i_zero j_next =
        (CrabbMatrix n ^ k) i_zero j_curr * CrabbMatrix n j_curr j_next := h_mul
    _ = (CrabbMatrix n ^ k) i_zero j_curr * crabbWeight n ⟨k, hk⟩ := by
      have hk' : j_curr.val < n - 1 := by
        simpa [j_curr] using hk
      have h_entry :
          CrabbMatrix n j_curr j_next = crabbWeight n ⟨j_curr.val, hk'⟩ :=
        crabb_entry_val (n := n) (i := j_curr) (j := j_next) h_cond hk'
      have h_val : j_curr.val = k := rfl
      simp [h_entry, h_val]

lemma pow_prod_form (hn : n ≥ 2) (k : ℕ) (hk : k ≤ n - 1) :
    (CrabbMatrix n ^ k) ⟨0, by omega⟩ ⟨k, by omega⟩ =
    ∏ i : Fin k, crabbWeight n ⟨i.val, by omega⟩ := by
  induction k with
  | zero =>
    simp
  | succ k ih =>
    have hk_lt : k < n - 1 := by omega
    have hk_le : k ≤ n - 1 := by omega
    rw [pow_recurrence (n := n) k hk_lt]
    rw [ih hk_le]
    rw [Fin.prod_univ_castSucc]
    congr 1

lemma crabb_power_corner_entry (hn : n ≥ 2) :
    (CrabbMatrix n ^ (n - 1)) ⟨0, by omega⟩ ⟨n - 1, by omega⟩ = 2 := by
  rw [pow_prod_form (n := n) hn (n - 1) (by rfl)]
  have h_prod_eq : (∏ i : Fin (n - 1), crabbWeight n ⟨i.val, by omega⟩) =
                   (∏ i : Fin (n - 1), crabbWeight n i) := by
    apply Finset.prod_congr rfl
    intro x _
    congr
  rw [h_prod_eq]
  exact crabb_weight_prod_eq_two hn

noncomputable section
abbrev Euc (n : ℕ) := EuclideanSpace ℂ (Fin n)

lemma matrix_toEuclideanLin_apply {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (M : Matrix m n ℂ) (v : EuclideanSpace ℂ n) :
    ((Matrix.toEuclideanLin M v).ofLp) = Matrix.mulVec M v.ofLp := by
  rfl

lemma matrix_toEuclideanLin_apply_coord {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (M : Matrix m n ℂ) (v : EuclideanSpace ℂ n) (i : m) :
    (Matrix.toEuclideanLin M v) i = (Matrix.mulVec M v) i := by
  simpa using congr_fun (matrix_toEuclideanLin_apply M v) i

lemma matrix_toEuclideanLin_apply_toLp {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (M : Matrix m n ℂ) (v : EuclideanSpace ℂ n) :
    Matrix.toEuclideanLin M v = WithLp.toLp (p := 2) (Matrix.mulVec M v) := by
  ext i
  simpa using matrix_toEuclideanLin_apply_coord M v i

lemma single_entry_action {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (i₀ j₀ : Fin n) (c : ℂ)
      (h : ∀ i j, M i j = if i = i₀ ∧ j = j₀ then c else 0) (v : EuclideanSpace ℂ (Fin n)) :
      (Matrix.toEuclideanLin M) v = (c * v j₀) • (PiLp.basisFun 2 ℂ (Fin n) i₀) := by
    ext k
    simp only [matrix_toEuclideanLin_apply, Matrix.mulVec, dotProduct, h, PiLp.basisFun_apply]
    by_cases hk : k = i₀
    · simp [hk]
    · simp [hk]

lemma single_entry_norm_image {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (i₀ j₀ : Fin n) (c : ℂ)
      (h : ∀ i j, M i j = if i = i₀ ∧ j = j₀ then c else 0) (v : EuclideanSpace ℂ (Fin n)) :
      ‖(Matrix.toEuclideanLin M) v‖ = ‖c‖ * ‖v j₀‖ := by
    rw [single_entry_action M i₀ j₀ c h v]
    rw [norm_smul]
    have h_norm_basis : ‖PiLp.basisFun 2 ℂ (Fin n) i₀‖ = 1 := by
      simp [PiLp.basisFun]
    rw [h_norm_basis, mul_one, norm_mul]


lemma single_entry_le_opNorm {n : ℕ}
      (M : Matrix (Fin n) (Fin n) ℂ) (i₀ j₀ : Fin n) (c : ℂ)
      (h : ∀ i j, M i j = if i = i₀ ∧ j = j₀ then c else 0) :
      ‖(Matrix.toEuclideanLin M).toContinuousLinearMap‖ ≤ ‖c‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ ?nonneg ?bound
    · exact norm_nonneg c
    · intro v
      change ‖(Matrix.toEuclideanLin M) v‖ ≤ ‖c‖ * ‖v‖
      have h_norm :
          ‖(Matrix.toEuclideanLin M) v‖ = ‖c‖ * ‖v j₀‖ :=
        single_entry_norm_image (M := M) (i₀ := i₀) (j₀ := j₀)
          (c := c) (h := h) v
      have h_coord : ‖v j₀‖ ≤ ‖v‖ := by
        let e : EuclideanSpace ℂ (Fin n) :=
          EuclideanSpace.single j₀ (1 : ℂ)
        have h_norm_e : ‖e‖ = (1 : ℝ) := by
          simp [e, EuclideanSpace.norm_single (i := j₀) (a := (1 : ℂ))]
        have h_inner_ofLp :
            ⟪e, v⟫ = v.ofLp j₀ := by
          simpa [e] using
            (EuclideanSpace.inner_single_left (i := j₀)
               (a := (1 : ℂ)) (v := v))
        have h_inner : ⟪e, v⟫ = v j₀ := by
          simpa using h_inner_ofLp
        calc
          ‖v j₀‖ = ‖⟪e, v⟫‖ := by simp [h_inner]
          _ ≤ ‖e‖ * ‖v‖      := norm_inner_le_norm e v
          _ = ‖v‖            := by simp [h_norm_e, one_mul]
      have := mul_le_mul_of_nonneg_left h_coord (norm_nonneg c)
      simpa [h_norm] using this

lemma single_entry_ge_opNorm {n : ℕ}
      (M : Matrix (Fin n) (Fin n) ℂ) (i₀ j₀ : Fin n) (c : ℂ)
      (h : ∀ i j, M i j = if i = i₀ ∧ j = j₀ then c else 0) :
      ‖c‖ ≤ ‖(Matrix.toEuclideanLin M).toContinuousLinearMap‖ := by
    classical
    haveI : Nonempty (Fin n) := ⟨i₀⟩
    let T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
      (Matrix.toEuclideanLin M).toContinuousLinearMap
    let e_j0 : EuclideanSpace ℂ (Fin n) :=
      PiLp.basisFun 2 ℂ (Fin n) j₀
    have h_norm_basis : ‖e_j0‖ = 1 := by
      simp [e_j0]
    have h_val : e_j0 j₀ = 1 := by
      simp [e_j0]
    have h_norm_Tej0 : ‖T e_j0‖ = ‖c‖ := by
      change ‖(Matrix.toEuclideanLin M) e_j0‖ = ‖c‖
      have h' :=
        single_entry_norm_image (M := M) (i₀ := i₀) (j₀ := j₀)
          (c := c) (h := h) (v := e_j0)
      have : ‖(Matrix.toEuclideanLin M) e_j0‖ = ‖c‖ * ‖(1 : ℂ)‖ := by
        simpa [h_val] using h'
      simpa [norm_one, mul_one] using this
    have h_le' : ‖c‖ ≤ ‖T‖ * 1 := by
      have h_le := ContinuousLinearMap.le_opNorm T e_j0
      simpa [h_norm_Tej0, h_norm_basis] using h_le
    have : ‖c‖ ≤ ‖T‖ := by
      simpa [one_mul] using h_le'
    simpa [T] using this

lemma norm_single_entry {n : ℕ}
      (M : Matrix (Fin n) (Fin n) ℂ) (i₀ j₀ : Fin n) (c : ℂ)
      (h : ∀ i j, M i j = if i = i₀ ∧ j = j₀ then c else 0) :
      ‖(Matrix.toEuclideanLin M).toContinuousLinearMap‖ = ‖c‖ := by
    apply le_antisymm
    · exact single_entry_le_opNorm (M := M) (i₀ := i₀) (j₀ := j₀) (c := c) (h := h)
    · exact single_entry_ge_opNorm (M := M) (i₀ := i₀) (j₀ := j₀) (c := c) (h := h)

end

lemma crabbMatrix_superdiag (i j : Fin n)
    (h_nz : CrabbMatrix n i j ≠ 0) :
    j.val = i.val + 1 := by
  classical
  by_contra h'
  have : CrabbMatrix n i j = 0 := by
    simp [CrabbMatrix, h']
  exact h_nz this

lemma crabb_power_single_entry
    (hn : n ≥ 2) :
    ∀ i j,
      (CrabbMatrix n ^ (n - 1)) i j =
        if i = ⟨0, by omega⟩ ∧ j = ⟨n - 1, by omega⟩
        then (2 : ℂ) else 0 := by
  classical
  have hA : ∀ i j, CrabbMatrix n i j ≠ 0 → j.val = i.val + 1 := by
    intro i j h_nz
    exact crabbMatrix_superdiag (n := n) i j h_nz
  intro i j
  by_cases hij : i = ⟨0, by omega⟩ ∧ j = ⟨n - 1, by omega⟩
  · rcases hij with ⟨hi, hj⟩
    subst hi; subst hj
    simp [crabb_power_corner_entry (n := n) (hn := hn)]
  · have nonzero_implies_special :
        (CrabbMatrix n ^ (n - 1)) i j ≠ 0 →
        i = ⟨0, by omega⟩ ∧ j = ⟨n - 1, by omega⟩ := by
      intro h_nz
      have h_spars :=
        superdiag_pow_sparsity (n := n)
          (A := CrabbMatrix n) hA (n - 1) i j h_nz
      have h_eq : j.val = i.val + (n - 1) := h_spars
      have hi0 : i.val = 0 := by
        have : i.val + (n - 1) < n := by
          simpa [h_eq] using j.is_lt
        omega
      have hj_last : j.val = n - 1 := by
        simpa [hi0] using h_eq
      have hi : i = ⟨0, by omega⟩ := by
        apply Fin.ext
        simp [hi0]
      have hj : j = ⟨n - 1, by omega⟩ := by
        apply Fin.ext
        simp [hj_last]
      exact ⟨hi, hj⟩
    have hzero : (CrabbMatrix n ^ (n - 1)) i j = 0 := by
      by_contra h_nz
      exact hij (nonzero_implies_special h_nz)
    simp [hij, hzero]

theorem crabb_poly_norm_eq_two
    (hn : n ≥ 2) :
    ‖(Matrix.toEuclideanLin (CrabbMatrix n ^ (n - 1))).toContinuousLinearMap‖ = 2 := by
  classical
  haveI : Nonempty (Fin n) := ⟨0, by omega⟩
  have h_shape :
      ∀ i j,
        (CrabbMatrix n ^ (n - 1)) i j =
          if i = ⟨0, by omega⟩ ∧ j = ⟨n - 1, by omega⟩
          then (2 : ℂ) else 0 :=
    crabb_power_single_entry (n := n) hn
  have h :=
    norm_single_entry
      (n := n)
      (M := CrabbMatrix n ^ (n - 1))
      (i₀ := ⟨0, by omega⟩)
      (j₀ := ⟨n - 1, by omega⟩)
      (c := (2 : ℂ))
      (h := fun i j => h_shape i j)
  simpa using h

end CrabbProperties

noncomputable abbrev crabbCLM (n : ℕ) :
    Euc n →L[ℂ] Euc n :=
  (Matrix.toEuclideanLin (CrabbMatrix n)).toContinuousLinearMap

section CrabbGeometry

open scoped BigOperators

variable {n : ℕ}

noncomputable def CrabbSym (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  let C := CrabbMatrix n
  C + C.conjTranspose

noncomputable def tridiagonalCharPoly (w : Fin (n - 1) → ℂ) : ℕ → Polynomial ℂ
  | 0 => 1
  | 1 => Polynomial.X
  | k+2 =>
      let w_val : ℂ := if h : k < n-1 then w ⟨k, h⟩ else 0
      Polynomial.X * tridiagonalCharPoly w (k+1) -
      Polynomial.C (Complex.normSq w_val : ℂ) * tridiagonalCharPoly w k

noncomputable def tridiagonalMatrix (w : Fin (n - 1) → ℂ) (k : ℕ) :
    Matrix (Fin k) (Fin k) ℂ :=
  let wVal : ℕ → ℂ := fun t => if h : t < n - 1 then w ⟨t, h⟩ else 0
  fun i j =>
    if _hji : j.val + 1 = i.val then star (wVal j.val)
    else if _hij : i.val + 1 = j.val then wVal i.val else 0

noncomputable def crabbVector (n : ℕ) (_hn : 2 ≤ n) :
    Fin n → ℂ :=
  let a : ℝ := 1 / Real.sqrt (2 * (n - 1))
  let b : ℝ := 1 / Real.sqrt (n - 1)
  fun i : Fin n =>
    if (i : ℕ) = 0 ∨ (i : ℕ) = n - 1 then (a : ℂ) else (b : ℂ)

lemma crabbVector_coord_boundary (hn : 2 ≤ n) :
    let x := crabbVector n hn
    let a : ℝ := 1 / Real.sqrt (2 * (n - 1))
    x ⟨0, by omega⟩ = (a : ℂ) ∧
    x ⟨n - 1, by omega⟩ = (a : ℂ) := by
  intro x a
  simp [x, crabbVector, a]

lemma crabbVector_coord_interior (hn : 2 ≤ n) :
    let x := crabbVector n hn
    let b : ℝ := 1 / Real.sqrt (n - 1)
    ∀ i : Fin n, (i : ℕ) ≠ 0 → (i : ℕ) ≠ n - 1 → x i = (b : ℂ) := by
  intro x b i hi0 hiLast
  simp_all [x, crabbVector, b]

lemma sum_boundary_interior {n : ℕ} (hn : 2 ≤ n) (f : Fin n → ℝ) (A B : ℝ)
    (h_bound : f ⟨0, by omega⟩ = A ∧ f ⟨n - 1, by omega⟩ = A)
    (h_inter : ∀ i : Fin n, (i : ℕ) ≠ 0 → (i : ℕ) ≠ n - 1 → f i = B) :
    ∑ i : Fin n, f i = 2 * A + (n - 2) * B := by
  let i₀ : Fin n := ⟨0, by omega⟩
  let i_last : Fin n := ⟨n - 1, by omega⟩
  have h_ne : i₀ ≠ i_last := by
    intro h
    have := congr_arg Fin.val h
    simp [i₀, i_last] at this
    omega
  let S_boundary : Finset (Fin n) := {i₀, i_last}
  let S_interior : Finset (Fin n) := Finset.univ \ S_boundary
  have h_subset : S_boundary ⊆ Finset.univ := Finset.subset_univ _
  rw [← Finset.sum_sdiff h_subset]
  have h_sum_bound : ∑ i ∈ S_boundary, f i = 2 * A := by
    simp only [S_boundary, Finset.sum_pair h_ne]
    rw [h_bound.1, h_bound.2]
    ring
  have h_sum_inter : ∑ i ∈ S_interior, f i = (n - 2 : ℝ) * B := by
    rw [Finset.sum_congr rfl]
    · rw [Finset.sum_const]
      rw [nsmul_eq_mul]
      congr
      simp only [S_interior]
      rw [Finset.card_univ_diff]
      simp only [S_boundary, Finset.card_pair h_ne, Fintype.card_fin]
      rw [Nat.cast_sub hn]
      norm_num
    · intro i hi
      simp only [S_interior, Finset.mem_sdiff, Finset.mem_univ, true_and, S_boundary] at hi
      rw [Finset.mem_insert, Finset.mem_singleton] at hi
      push_neg at hi
      apply h_inter
      · intro h0
        apply hi.1
        apply Fin.ext
        exact h0
      · intro hLast
        apply hi.2
        apply Fin.ext
        exact hLast
  rw [h_sum_bound, h_sum_inter]
  ring

lemma norm_crabbVector (hn : 2 ≤ n) :
    ‖(WithLp.equiv 2 (Fin n → ℂ)).symm (crabbVector n hn)‖ = 1 := by
  let v := (WithLp.equiv 2 (Fin n → ℂ)).symm (crabbVector n hn)
  let a : ℝ := 1 / Real.sqrt (2 * (n - 1))
  let b : ℝ := 1 / Real.sqrt (n - 1)
  have h1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have h2 : (0 : ℝ) < 2 * ((n : ℝ) - 1) := by linarith
  have ha : 0 < a := by
    dsimp [a]
    exact div_pos (by norm_num) (Real.sqrt_pos.mpr h2)
  have hb : 0 < b := by
    dsimp [b]
    exact div_pos (by norm_num) (Real.sqrt_pos.mpr h1)
  have h_norm_sq : ‖v‖^2 = ∑ i : Fin n, ‖v i‖^2 := by
    rw [PiLp.norm_sq_eq_of_L2]
  have H_bound : ‖(a : ℂ)‖ ^ 2 = a ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
  have H_inter : ‖(b : ℂ)‖ ^ 2 = b ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb]
  have h_sum_val : ∑ i : Fin n, ‖v i‖^2 = 2 * a^2 + (n - 2) * b^2 := by
    apply sum_boundary_interior hn (fun i => ‖v i‖^2) (a^2) (b^2)
    · constructor
      · simp only [v, WithLp.equiv_symm_apply]
        rw [show crabbVector n hn ⟨0, by omega⟩ = (a : ℂ) from (crabbVector_coord_boundary hn).1]
        exact H_bound
      · simp only [v, WithLp.equiv_symm_apply]
        rw [show crabbVector n hn ⟨n - 1, by omega⟩ =
        (a : ℂ) from (crabbVector_coord_boundary hn).2]
        exact H_bound
    · intro i h0 hl
      simp only [v, WithLp.equiv_symm_apply]
      rw [crabbVector_coord_interior hn i h0 hl]
      exact H_inter
  have h_alg : 2 * a^2 + ((n : ℝ) - 2) * b^2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow]
    simp only [one_pow]
    have h1' : 0 ≤ (n : ℝ) - 1 := le_of_lt h1
    have h2' : 0 ≤ 2 * ((n : ℝ) - 1) := le_of_lt h2
    rw [Real.sq_sqrt h2', Real.sq_sqrt h1']
    have : (n : ℝ) - 1 ≠ 0 := by linarith
    field_simp
    ring
  rw [h_sum_val, h_alg] at h_norm_sq
  calc
    ‖v‖ = Real.sqrt (‖v‖^2) := by
      rw [Real.sqrt_sq (norm_nonneg _)]
    _ = Real.sqrt 1 := by rw [h_norm_sq]
    _ = 1 := by norm_num

noncomputable def crabbVecEuc (n : ℕ) (hn : 2 ≤ n) : Euc n :=
  (WithLp.equiv 2 (Fin n → ℂ)).symm (crabbVector n hn)

lemma crabbVecEuc_norm_one (hn : 2 ≤ n) :
    ‖crabbVecEuc n hn‖ = 1 := by
  unfold crabbVecEuc
  simpa using (norm_crabbVector (n := n) hn)

lemma crabbVecEuc_coord_boundary (hn : 2 ≤ n) :
    let x := crabbVecEuc n hn
    let a : ℝ := 1 / Real.sqrt (2 * (n - 1))
    x ⟨0, by omega⟩ = (a : ℂ) ∧
    x ⟨n - 1, by omega⟩ = (a : ℂ) := by
  intro x a
  simp only [x, crabbVecEuc, WithLp.equiv_symm_apply]
  exact crabbVector_coord_boundary hn

lemma crabbVecEuc_coord_interior (hn : 2 ≤ n) :
    let x := crabbVecEuc n hn
    let b : ℝ := 1 / Real.sqrt (n - 1)
    ∀ i : Fin n, (i : ℕ) ≠ 0 → (i : ℕ) ≠ n - 1 → x i = (b : ℂ) := by
  intro x b i hi0 hiLast
  simp only [x, crabbVecEuc, WithLp.equiv_symm_apply]
  exact crabbVector_coord_interior hn i hi0 hiLast

lemma crabbCLM_coord {n : ℕ} (hn : n ≥ 2) (v : Euc n) (i : Fin n) :
    (crabbCLM n v) i =
    if h : i.val < n - 1 then
      crabbWeight n ⟨i.val, h⟩ * v ⟨i.val + 1, by omega⟩
    else
      0 := by
  dsimp [crabbCLM]
  simp only [Matrix.mulVec, dotProduct]
  split_ifs with h_lt
  · let j_target : Fin n := ⟨i.val + 1, by omega⟩
    rw [Finset.sum_eq_single j_target]
    · dsimp only [j_target]
      rw [crabb_entry_val _ _ rfl h_lt]
    · intro j _ hj_ne
      rw [CrabbMatrix, dif_neg]
      · simp
      · intro h_eq
        apply hj_ne
        apply Fin.ext
        simp only [j_target]
        omega
    · simp
  · apply Finset.sum_eq_zero
    intro j _
    rw [CrabbMatrix, dif_neg]
    · simp
    · intro h_eq
      have : j.val = i.val + 1 := h_eq
      omega

lemma inner_crabbCLM_as_real_sum {n : ℕ} (hn : n ≥ 2) (v : Euc n)
    (hv_real : ∀ k, (v k).im = 0) :
    ⟪crabbCLM n v, v⟫ =
    ∑ i : Fin (n - 1),
      (crabbWeight n i) *
      (v ⟨i.val + 1, by omega⟩) *
      (v ⟨i.val,     by omega⟩) := by
  classical
  set m : ℕ := n - 1 with hm
  have h1n : (1 : ℕ) ≤ n := by
    exact (le_trans (by decide : (1 : ℕ) ≤ 2) hn)
  have hmn' : n - 1 + 1 = n := Nat.sub_add_cancel h1n
  have hmn : m + 1 = n := by
    simpa [hm] using hmn'
  rw [PiLp.inner_apply]
  rw [← Equiv.sum_comp (finCongr hmn), Fin.sum_univ_castSucc]
  rw [crabbCLM_coord hn v, dif_neg (by simp [hm]), inner_zero_left, add_zero]
  apply Finset.sum_congr rfl
  intro i _
  rw [crabbCLM_coord hn v, dif_pos (by simp []; omega)]
  simp only [crabbWeight, mul_comm, mul_ite]
  have h_idx : finCongr hmn i.castSucc = ⟨i.val, by omega⟩ := Fin.ext (by simp)
  simp only [h_idx]
  split_ifs <;>
  {
    simp only [inner, Inner.inner]
    simp only [map_mul, map_one,
          Complex.conj_ofReal, Complex.conj_eq_iff_im.mpr (hv_real _)]
    ring
  }

lemma real_sum_for_crabbVecEuc {n : ℕ} (hn : n ≥ 2) :
    ∑ i : Fin (n - 1),
        (crabbWeight n i) *
        (crabbVecEuc n hn ⟨i.val + 1, by omega⟩) *
        (crabbVecEuc n hn ⟨i.val, by omega⟩) = 1 := by
    let x := crabbVecEuc n hn
    let a : ℝ := 1 / Real.sqrt (2 * (n - 1))
    let b : ℝ := 1 / Real.sqrt (n - 1)
    have hx0 : x ⟨0, by omega⟩ = (a : ℂ) := (crabbVecEuc_coord_boundary hn).1
    have hxn : x ⟨n - 1, by omega⟩ = (a : ℂ) := (crabbVecEuc_coord_boundary hn).2
    have h_inter :
        ∀ k : Fin n, (k : ℕ) ≠ 0 → (k : ℕ) ≠ n - 1 → x k = (b : ℂ) :=
      crabbVecEuc_coord_interior hn
    by_cases h2 : n = 2
    · subst h2
      simp only []
      unfold crabbWeight
      rw [Fin.sum_univ_one]
      simp only [Fin.val_zero, zero_add, ↓reduceIte]
      rw [
        show (⟨1, by omega⟩ : Fin 2) = ⟨2 - 1, by omega⟩ from rfl,
        hxn,
        hx0
      ]
      dsimp [a]
      field_simp; norm_num
    · have hn_gt : n > 2 := by omega
      let i_start : Fin (n - 1) := ⟨0, by omega⟩
      let i_end : Fin (n - 1) := ⟨n - 2, by omega⟩
      have h_ne : i_start ≠ i_end := by
        intro h
        simp [i_start, i_end] at h
        omega
      let S : Finset (Fin (n - 1)) := {i_start, i_end}
      rw [← Finset.sum_sdiff (Finset.subset_univ S)]
      have h_boundary :
          ∑ i ∈ S,
              crabbWeight n i * x ⟨i.val + 1, by omega⟩ * x ⟨i.val, by omega⟩ =
            2 * Real.sqrt 2 * a * b := by
        rw [Finset.sum_pair h_ne]
        have w_start : crabbWeight n i_start = Real.sqrt 2 := by
          unfold crabbWeight
          have h1 : i_start.val = 0 := rfl
          have h2 : i_start.val ≠ n - 2 := by simp [i_start]; omega
          rw [if_pos h1, if_neg h2]; simp
        have w_end : crabbWeight n i_end = Real.sqrt 2 := by
          unfold crabbWeight
          have h1 : i_end.val = n - 2 := rfl
          have h2 : i_end.val ≠ 0 := by omega
          rw [if_neg h2, if_pos h1]; simp
        have x0 : x ⟨i_start.val, by omega⟩ = a := by simp [hx0, i_start]
        have x1 : x ⟨i_start.val + 1, by omega⟩ = b := by
          apply h_inter
          · simp [i_start]
          · simp [i_start]; omega
        have xn2 : x ⟨i_end.val, by omega⟩ = b := by
          apply h_inter
          · have : (n - 2 : ℕ) ≠ 0 := by omega
            simpa [i_end] using this
          · have : (n - 2 : ℕ) ≠ n - 1 := by omega
            simpa [i_end] using this
        have xn1 : x ⟨i_end.val + 1, by omega⟩ = a := by
          have h :
              (⟨i_end.val + 1, by omega⟩ : Fin n) = ⟨n - 1, by omega⟩ := by
            apply Fin.ext
            simp [i_end]; omega
          rw [h, hxn]
        rw [w_start, w_end, x0, x1, xn2, xn1]
        ring
      have h_interior :
          ∑ i ∈ (Finset.univ \ S),
              crabbWeight n i * x ⟨i.val + 1, by omega⟩ * x ⟨i.val, by omega⟩ =
            (n - 3) * b^2 := by
        rw [Finset.sum_congr rfl (fun i hi => ?_)]
        · rw [Finset.sum_const, nsmul_eq_mul]
          congr
          rw [Finset.card_univ_diff]
          simp only [S, Fintype.card_fin, Finset.card_pair h_ne]
          rw [Nat.sub_sub, Nat.cast_sub (by omega)]; norm_num
        · have hiS : i ∉ S := Finset.mem_sdiff.1 hi |>.2
          have h_val0 : i.val ≠ 0 := by
            intro h
            have : i = i_start := Fin.ext h
            exact hiS (Finset.mem_insert.mpr (Or.inl this))
          have h_valn2 : i.val ≠ n - 2 := by
            intro h
            have : i = i_end := Fin.ext h
            exact hiS (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr this)))
          have hx_i : x ⟨i.val, by omega⟩ = (b : ℂ) := by
            apply h_inter ⟨i.val, by omega⟩
            · exact_mod_cast h_val0
            · intro h
              have : i.val = n - 1 := by omega
              omega
          have hx_i1 : x ⟨i.val + 1, by omega⟩ = (b : ℂ) := by
            apply h_inter ⟨i.val + 1, by omega⟩
            · simp
            · intro h
              have : i.val + 1 = n - 1 := h
              omega
          unfold crabbWeight
          rw [if_neg h_val0, if_neg h_valn2]
          simp [hx_i, hx_i1]
          ring
      rw [h_boundary, h_interior]
      dsimp [a, b]
      have h_pos : (0 : ℝ) < (n : ℝ) - 1 := by
        have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        linarith
      have h_goal_real :
        (↑n - 3 : ℝ) * (1 / Real.sqrt (↑n - 1)) ^ 2
          + 2 * Real.sqrt 2 *
            (1 / Real.sqrt (2 * (↑n - 1))) *
            (1 / Real.sqrt (↑n - 1)) = 1 := by
        have h_sqrt_ne : Real.sqrt (↑n - 1) ≠ 0 :=
          Real.sqrt_ne_zero'.mpr h_pos
        have h2_pos : (0 : ℝ) < 2 * (↑n - 1) := by
          have : (0 : ℝ) < (↑n - 1) := h_pos
          have h2 : (0 : ℝ) < (2 : ℝ) := by norm_num
          nlinarith
        have h_sqrt2n_ne : Real.sqrt (2 * (↑n - 1)) ≠ 0 :=
          Real.sqrt_ne_zero'.mpr h2_pos
        have h_sqrt2_ne : Real.sqrt 2 ≠ 0 :=
          Real.sqrt_ne_zero'.mpr (by norm_num)
        rw [Real.sqrt_mul (by norm_num : 0 ≤ (2 : ℝ))]
        field_simp [one_div, pow_two, h_sqrt_ne, h_sqrt2_ne, h_sqrt2n_ne]
        rw [Real.sq_sqrt (le_of_lt h_pos)]
        ring_nf
      have h_goal_complex :
        ((↑n - 3 : ℝ) * (1 / Real.sqrt (↑n - 1)) ^ 2
          + 2 * Real.sqrt 2 *
          (1 / Real.sqrt (2 * (↑n - 1))) *
          (1 / Real.sqrt (↑n - 1)) : ℂ) = (1 : ℂ) := by
        exact_mod_cast h_goal_real
      simpa [x, a, b] using h_goal_complex

lemma inner_crabbCLM_crabbVecEuc (hn : 2 ≤ n) :
    ⟪crabbCLM n (crabbVecEuc n hn), crabbVecEuc n hn⟫ = (1 : ℂ) := by
  have hv_real : ∀ k, ((crabbVecEuc n hn) k).im = 0 := by
    intro k
    simp only [crabbVecEuc, WithLp.equiv_symm_apply]
    unfold crabbVector
    by_cases h : (k : ℕ) = 0 ∨ (k : ℕ) = n - 1
    · rw [if_pos h]
      simp
    · rw [if_neg h]
      simp
  have h_sum := inner_crabbCLM_as_real_sum hn (crabbVecEuc n hn) hv_real
  rw [h_sum]
  exact real_sum_for_crabbVecEuc hn

lemma exists_vector_numerical_value_one (hn : n ≥ 2) :
    ∃ x : EuclideanSpace ℂ (Fin n), ‖x‖ = 1 ∧ ⟪crabbCLM n x, x⟫ = 1 := by
  refine ⟨crabbVecEuc n hn, ?_, ?_⟩
  · simpa using (crabbVecEuc_norm_one (n := n) hn)
  · simpa using (inner_crabbCLM_crabbVecEuc (n := n) hn)

noncomputable def hermitianPart (n : ℕ) :
    Matrix (Fin n) (Fin n) ℂ :=
  (1 / 2 : ℂ) • (CrabbMatrix n + (CrabbMatrix n).conjTranspose)

noncomputable def hermitianCLM (n : ℕ) :
    Euc n →L[ℂ] Euc n :=
  (1 / 2 : ℂ) • (crabbCLM n + (crabbCLM n).adjoint)

lemma inner_adjoint_eq_flip (T : Euc n →L[ℂ] Euc n) (x : Euc n) :
    ⟪T.adjoint x, x⟫ = ⟪x, T x⟫ := by
  simpa using
    (ContinuousLinearMap.adjoint_inner_left (A := T) (x := x) (y := x))


lemma inner_hermitianCLM (x : Euc n) :
    ⟪hermitianCLM n x, x⟫ =
      (1 / 2 : ℂ) * (⟪crabbCLM n x, x⟫ + ⟪(crabbCLM n).adjoint x, x⟫) := by
  classical
  unfold hermitianCLM
  simp [mul_add]
  ring

lemma real_inner_adjoint_eq (T : Euc n →L[ℂ] Euc n) (x : Euc n) :
    Complex.re (⟪T.adjoint x, x⟫) = Complex.re (⟪T x, x⟫) := by
  have h1 : ⟪T.adjoint x, x⟫ = ⟪x, T x⟫ :=
    inner_adjoint_eq_flip (T := T) (x := x)
  have h2 : ⟪x, T x⟫ = star ⟪T x, x⟫ := (inner_conj_symm x (T x)).symm
  rw [h1, h2]
  apply Complex.conj_re

lemma inner_eq_real_part (x : Euc n) :
    Complex.re (⟪crabbCLM n x, x⟫) =
    Complex.re (⟪hermitianCLM n x, x⟫) := by
  let T : Euc n →L[ℂ] Euc n := crabbCLM n
  have h1 :
      ⟪hermitianCLM n x, x⟫ =
        (1 / 2 : ℂ) * (⟪T x, x⟫ + ⟪T.adjoint x, x⟫) := by
    simpa [hermitianCLM, T] using
      (inner_hermitianCLM (n := n) (x := x))
  have h2 :
      Complex.re (⟪hermitianCLM n x, x⟫) =
        (1 / 2 : ℝ) *
          (Complex.re (⟪T x, x⟫) + Complex.re (⟪T.adjoint x, x⟫)) := by
    simp [h1, Complex.mul_re, Complex.add_re, mul_add]
  have h3 : Complex.re (⟪T.adjoint x, x⟫) =
      Complex.re (⟪T x, x⟫) :=
    real_inner_adjoint_eq (T := T) (x := x)
  have h4 :
      (1 / 2 : ℝ) *
          (Complex.re (⟪T x, x⟫) + Complex.re (⟪T.adjoint x, x⟫)) =
        Complex.re (⟪T x, x⟫) := by
    have h_sum :
        (1 / 2 : ℝ) *
            (Complex.re (⟪T x, x⟫) + Complex.re (⟪T x, x⟫)) =
          Complex.re (⟪T x, x⟫) := by
      ring
    simpa [h3, two_mul, add_comm, add_left_comm, add_assoc] using h_sum
  have : Complex.re (⟪hermitianCLM n x, x⟫) =
      Complex.re (⟪T x, x⟫) := by
    exact h2.trans h4
  exact this.symm

lemma hermitianCLM_self_adjoint (n : ℕ) :
    ∀ x y, ⟪hermitianCLM n x, y⟫ = ⟪x, hermitianCLM n y⟫ := by
  intro x y
  unfold hermitianCLM
  have h_left : ⟪((1 / 2 : ℂ) • (crabbCLM n + (crabbCLM n).adjoint)) x, y⟫ =
      (1 / 2 : ℂ) * (⟪crabbCLM n x, y⟫ + ⟪(crabbCLM n).adjoint x, y⟫) := by
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
      inner_smul_left, inner_add_left, map_div₀, map_one, map_ofNat]
  have h_right : ⟪x, ((1 / 2 : ℂ) • (crabbCLM n + (crabbCLM n).adjoint)) y⟫ =
      (1 / 2 : ℂ) * (⟪x, crabbCLM n y⟫ + ⟪x, (crabbCLM n).adjoint y⟫) := by
    rw [ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.add_apply, inner_smul_right, inner_add_right]
  rw [h_left, h_right]
  have h1 : ⟪(crabbCLM n).adjoint x, y⟫ = ⟪x, crabbCLM n y⟫ :=
    ContinuousLinearMap.adjoint_inner_left (crabbCLM n) y x
  have h2 : ⟪x, (crabbCLM n).adjoint y⟫ = ⟪crabbCLM n x, y⟫ := by
    calc
      ⟪x, (crabbCLM n).adjoint y⟫ =
        star ⟪(crabbCLM n).adjoint y, x⟫ := Eq.symm (inner_conj_symm x ((crabbCLM n).adjoint y))
      _ = star ⟪y, crabbCLM n x⟫ := by rw [ContinuousLinearMap.adjoint_inner_left (crabbCLM n) x y]
      _ = ⟪crabbCLM n x, y⟫ := inner_conj_symm (crabbCLM n x) y
  rw [h1, h2]
  ring

lemma quadratic_form_self_adjoint_real
    {E : Type*} [NormedAddCommGroup E] [CompleteSpace E] [InnerProductSpace ℂ E]
    (A : E →L[ℂ] E) (hA : A.adjoint = A) (x : E) :
    Complex.im ⟪A x, x⟫ = 0 := by
  have h_conj :
      (starRingEnd ℂ) ⟪A x, x⟫ = ⟪A x, x⟫ := by
    have h₁ : ⟪A x, x⟫ = ⟪x, A x⟫ := by
      simpa [hA] using
        (ContinuousLinearMap.adjoint_inner_left (A := A) (x := x) (y := x)
          : ⟪A.adjoint x, x⟫ = ⟪x, A x⟫)
    have h₂ : ⟪x, A x⟫ = (starRingEnd ℂ) ⟪A x, x⟫ := by
      simp [inner_conj_symm]
    exact (h₁.trans h₂).symm
  exact (Complex.conj_eq_iff_im.mp h_conj)

lemma norm_sq_decomposition (x : Euc n) :
    Complex.normSq (⟪crabbCLM n x, x⟫) =
      (Complex.re (⟪hermitianCLM n x, x⟫))^2 +
      (Complex.im (⟪crabbCLM n x, x⟫))^2 := by
  classical
  set z : ℂ := ⟪crabbCLM n x, x⟫
  have h_re :
      Complex.re (⟪hermitianCLM n x, x⟫) = Complex.re z := by
    simpa [z] using (inner_eq_real_part (n := n) (x := x)).symm
  have h_norm : Complex.normSq z = z.re^2 + z.im^2 := by
    simp [Complex.normSq, pow_two]
  have h_goal :
      Complex.normSq z =
        (Complex.re (⟪hermitianCLM n x, x⟫))^2 +
        (Complex.im z)^2 := by
    simpa [h_re] using h_norm
  simpa [z] using h_goal

lemma crabbMatrix_diag (n : ℕ) (i : Fin n) :
  CrabbMatrix n i i = 0 := by
  classical
  simp [CrabbMatrix]

lemma crabbMatrix_conjTranspose_subdiag (n : ℕ) (i j : Fin n) :
  (CrabbMatrix n).conjTranspose i j ≠ 0 →
  i.val = j.val + 1 := by
  classical
  intro h_nonzero
  by_cases hji : i.val = j.val + 1
  · exact hji
  · have h_zero : (CrabbMatrix n).conjTranspose i j = 0 := by
      simp [Matrix.conjTranspose_apply, CrabbMatrix, hji]
    exact (h_nonzero h_zero).elim

lemma hermitianPart_superdiag (n : ℕ)
    (i : Fin n) (h : i.val < n - 1) :
  hermitianPart n i ⟨i.val + 1, by omega⟩ =
    (crabbWeight n ⟨i.val, h⟩) / 2 := by
  classical
  have h_ct_zero :
      (CrabbMatrix n).conjTranspose i ⟨i.val + 1, by omega⟩ = 0 := by
    have hne : i.val ≠ (⟨i.val + 1, by omega⟩ : Fin n).val + 1 := by
      nlinarith
    have h_sub :=
      crabbMatrix_conjTranspose_subdiag (n := n) (i := i)
        (j := ⟨i.val + 1, by omega⟩)
    have : ¬(CrabbMatrix n).conjTranspose i ⟨i.val + 1, by omega⟩ ≠ 0 := by
      intro h_nonzero
      exact hne (h_sub h_nonzero)
    exact not_not.mp this
  have h_super :
      CrabbMatrix n i ⟨i.val + 1, by omega⟩ = crabbWeight n ⟨i.val, h⟩ := by
    simp [CrabbMatrix]
  rw [hermitianPart]
  simp only [Matrix.smul_apply, Matrix.add_apply, h_super, h_ct_zero]
  simp only [add_zero, smul_eq_mul]
  ring

lemma hermitianPart_subdiag (n : ℕ)
    (i : Fin n) (h : i.val < n - 1) :
  hermitianPart n ⟨i.val + 1, by omega⟩ i =
    star ((crabbWeight n ⟨i.val, h⟩) / 2) := by
  classical
  rw [hermitianPart]
  simp only [Matrix.smul_apply, Matrix.add_apply]
  have h_mat : CrabbMatrix n ⟨i.val + 1, by omega⟩ i = 0 := by
    unfold CrabbMatrix
    rw [dif_neg]
    · simp only []; omega
  have h_ct : (CrabbMatrix n).conjTranspose ⟨i.val + 1, by omega⟩ i =
      star (crabbWeight n ⟨i.val, h⟩) := by
    simp only [Matrix.conjTranspose_apply]
    have h_entry : CrabbMatrix n i ⟨i.val + 1, by omega⟩ = crabbWeight n ⟨i.val, h⟩ := by
      simp [CrabbMatrix]
    rw [h_entry]
  rw [h_mat, h_ct]
  simp only [zero_add, smul_eq_mul]
  simp only [div_eq_mul_inv]
  rw [StarMul.star_mul]
  rw [star_inv₀]
  simp []

lemma hermitianPart_far_zero (n : ℕ) (i j : Fin n)
    (h_far : (i.val + 1 < j.val) ∨ (j.val + 1 < i.val)) :
  hermitianPart n i j = 0 := by
  unfold hermitianPart
  simp only [Matrix.smul_apply, Matrix.add_apply]
  have h1 : CrabbMatrix n i j = 0 := by
    unfold CrabbMatrix
    rw [dif_neg]
    omega
  have h2 : (CrabbMatrix n).conjTranspose i j = 0 := by
    simp only [Matrix.conjTranspose_apply]
    unfold CrabbMatrix
    rw [dif_neg]
    · simp
    omega
  rw [h1, h2]
  simp

lemma hermitianPart_eq_tridiagonal (n : ℕ) :
  hermitianPart n = tridiagonalMatrix (fun i => (crabbWeight n i) / 2) n := by
  classical
  ext i j
  by_cases h_sub : j.val + 1 = i.val
  · have h_bound : j.val < n - 1 := by
      have hi := i.is_lt
      have : j.val + 1 < n := by simp [h_sub, hi]
      omega
    have h_i_eq : i = ⟨j.val + 1, by omega⟩ := Fin.ext h_sub.symm
    have h_left :
        hermitianPart n i j =
          star (crabbWeight n ⟨j.val, h_bound⟩ / 2) := by
      have h_subdiag := hermitianPart_subdiag (n := n) (i := j) h_bound
      simpa [h_i_eq] using h_subdiag
    have h_right :
        tridiagonalMatrix (fun i => (crabbWeight n i) / 2) n i j =
          star (crabbWeight n ⟨j.val, h_bound⟩ / 2) := by
      simp only [tridiagonalMatrix, h_sub, h_bound]
      rfl
    exact h_left.trans h_right.symm
  · by_cases h_super : i.val + 1 = j.val
    · have h_bound : i.val < n - 1 := by
        have hj := j.is_lt
        have : i.val + 1 < n := by simp [h_super, hj]
        omega
      have h_j_eq : j = ⟨i.val + 1, by omega⟩ := Fin.ext h_super.symm
      have h_left :
          hermitianPart n i j = crabbWeight n ⟨i.val, h_bound⟩ / 2 := by
        have h_superdiag := hermitianPart_superdiag (n := n) (i := i) h_bound
        simpa [h_j_eq] using h_superdiag
      have h_right :
          tridiagonalMatrix (fun i => (crabbWeight n i) / 2) n i j =
            crabbWeight n ⟨i.val, h_bound⟩ / 2 := by
        simp [tridiagonalMatrix, h_sub, h_super, h_bound]
      exact h_left.trans h_right.symm
    · have h_goal : hermitianPart n i j = 0 := by
        by_cases h_eq : i = j
        · subst h_eq
          simp [hermitianPart, Matrix.smul_apply, Matrix.add_apply,
            crabbMatrix_diag, Matrix.conjTranspose_apply]
        · have h_ne_val : i.val ≠ j.val := by
            intro h
            apply h_eq
            exact Fin.ext h
          have h_lt_or_gt : i.val < j.val ∨ j.val < i.val :=
            lt_or_gt_of_ne h_ne_val
          have h_far : (i.val + 1 < j.val) ∨ (j.val + 1 < i.val) := by
            cases h_lt_or_gt with
            | inl hlt =>
                have h_le : i.val + 1 ≤ j.val := Nat.succ_le_of_lt hlt
                exact Or.inl (lt_of_le_of_ne h_le h_super)
            | inr hgt =>
                have h_le : j.val + 1 ≤ i.val := Nat.succ_le_of_lt hgt
                exact Or.inr (lt_of_le_of_ne h_le h_sub)
          exact hermitianPart_far_zero (n := n) i j h_far
      simpa [tridiagonalMatrix, h_sub, h_super] using h_goal

end CrabbGeometry

section TridiagonalRecurrence

open Matrix BigOperators Polynomial

variable {n : ℕ}

noncomputable def charMatrix {n : ℕ} (w : Fin (n - 1) → ℂ) (k : ℕ) : Matrix (Fin k) (Fin k) (Polynomial ℂ) :=
  (Polynomial.X : Polynomial ℂ) • (1 : Matrix (Fin k) (Fin k) (Polynomial ℂ)) -
  (tridiagonalMatrix w k).map Polynomial.C

lemma charMatrix_zero_det {n : ℕ} (w : Fin (n - 1) → ℂ) :
    (charMatrix w 0).det = 1 := by
  simp [charMatrix]

lemma charMatrix_one_det {n : ℕ} (w : Fin (n - 1) → ℂ) :
    (charMatrix w 1).det = Polynomial.X := by
  simp [charMatrix, tridiagonalMatrix]

lemma charMatrix_diag {n : ℕ} (w : Fin (n - 1) → ℂ) (k : ℕ) (i : Fin k) :
    charMatrix w k i i = Polynomial.X := by
  simp [charMatrix, tridiagonalMatrix]

lemma charMatrix_super {n : ℕ} (w : Fin (n - 1) → ℂ) (k : ℕ) (i : Fin k) (j : Fin k)
    (h : j.val = i.val + 1) (hk : i.val < n - 1) :
    charMatrix w k i j = -Polynomial.C (w ⟨i.val, hk⟩) := by
  simp only [charMatrix, tridiagonalMatrix, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.map_apply, Matrix.one_apply]
  rw [if_neg, dif_neg, dif_pos]
  · simp only [hk, dif_pos, smul_zero, zero_sub]
  · simp [h]
  · intro heq
    rw [h] at heq
    omega
  · intro heq
    rw [Fin.ext_iff] at heq
    rw [h] at heq
    omega

lemma charMatrix_sub {n : ℕ} (w : Fin (n - 1) → ℂ) (k : ℕ) (i : Fin k) (j : Fin k)
    (h : i.val = j.val + 1) (hk : j.val < n - 1) :
    charMatrix w k i j = -Polynomial.C (star (w ⟨j.val, hk⟩)) := by
  simp only [charMatrix, tridiagonalMatrix, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.map_apply, Matrix.one_apply]
  rw [if_neg, dif_pos]
  · simp only [hk, dif_pos, smul_zero, zero_sub]
  · rw [h]
  · intro heq
    rw [Fin.ext_iff] at heq
    rw [h] at heq
    omega

lemma charMatrix_far {n : ℕ} (w : Fin (n - 1) → ℂ) (k : ℕ) (i j : Fin k)
    (h : i.val ≠ j.val ∧ i.val ≠ j.val + 1 ∧ j.val ≠ i.val + 1) :
    charMatrix w k i j = 0 := by
  simp only [charMatrix, tridiagonalMatrix, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.map_apply, Matrix.one_apply]
  rw [if_neg, dif_neg, dif_neg]
  · simp
  · exact h.2.2.symm
  · exact h.2.1.symm
  · exact Fin.ne_of_val_ne h.1

lemma charMatrix_submatrix_cast {k : ℕ} (w : Fin (k + 1) → ℂ) :
    (charMatrix (n := k + 2) w (k + 2)).submatrix (Fin.castSucc) (Fin.castSucc) =
    charMatrix (n := k + 1) (fun (i : Fin k) => w i.castSucc) (k + 1) := by
  ext i j
  simp only [charMatrix, Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply, 
             Matrix.map_apply, Matrix.one_apply]
  congr 1
  simp only [Fin.castSucc_inj]
  simp only [tridiagonalMatrix, Fin.val_castSucc]
  split_ifs <;> simp_all <;> omega

lemma charMatrix_minor_col_zero {k : ℕ} (w : Fin (k + 1) → ℂ) (i : Fin k) :
    let A := charMatrix (n := k + 2) w (k + 2)
    let Minor := A.submatrix Fin.castSucc (Fin.succAbove ⟨k, by omega⟩)
    Minor (i.castSucc) (Fin.last k) = 0 := by
  intro A Minor
  have h_col : (Fin.succAbove ⟨k, by omega⟩) (Fin.last k) = Fin.last (k + 1) := by
    unfold Fin.succAbove
    simp only [Fin.val_last, Fin.val_castSucc, Fin.lt_def]
    split_ifs
    · exfalso; omega
    · rfl
  dsimp [Minor]
  rw [h_col]
  apply charMatrix_far
  simp only [Fin.val_last, Fin.val_castSucc]
  refine ⟨?_, ?_, ?_⟩
  · omega
  · omega 
  · omega

lemma charMatrix_minor_corner {k : ℕ} (w : Fin (k + 1) → ℂ) :
    let A := charMatrix (n := k + 2) w (k + 2)
    let Minor := A.submatrix Fin.castSucc (Fin.succAbove ⟨k, by omega⟩)
    Minor (Fin.last k) (Fin.last k) = -Polynomial.C (w ⟨k, by omega⟩) := by
  intro A Minor
  have h_row : Fin.castSucc (Fin.last k) = ⟨k, by omega⟩ := by
    simp [Fin.castSucc, Fin.last]
  have h_col : Fin.succAbove ⟨k, by omega⟩ (Fin.last k) = Fin.last (k + 1) := by
    unfold Fin.succAbove
    simp only [Fin.val_last, Fin.val_castSucc, Fin.lt_def]
    split_ifs
    · exfalso; omega
    rfl
  dsimp [Minor]
  rw [h_row, h_col]
  apply charMatrix_super
  · simp [Fin.last]

lemma charMatrix_minor_sub {k : ℕ} (w : Fin (k + 1) → ℂ) :
    let A := charMatrix (n := k + 2) w (k + 2)
    let Minor := A.submatrix Fin.castSucc (Fin.succAbove ⟨k, by omega⟩)
    Minor.submatrix Fin.castSucc Fin.castSucc =
      charMatrix (n := k + 1) (fun i => w i.castSucc) k := by
  ext i j
  simp only [charMatrix, Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply,
             Matrix.map_apply, Matrix.one_apply]
  congr 1
  simp only [tridiagonalMatrix, Fin.val_castSucc]
  have h_idx : Fin.succAbove ⟨k, by omega⟩ (Fin.castSucc j) =
               Fin.castSucc (Fin.castSucc j) := by
    unfold Fin.succAbove
    split_ifs with h_lt
    · rfl
    · exfalso
      simp only [Fin.val_castSucc, Fin.lt_def] at h_lt
      omega
  rw [h_idx]
  simp only [Fin.val_castSucc]
  have h1 : ∀ x : Fin k, ↑x < k := fun x ↦ x.is_lt
  have h2 : ∀ x : Fin k, ↑x < k + 1 := fun x ↦ Nat.lt_succ_of_lt x.is_lt
  simp [h1, h2]
  split_ifs <;> simp_all <;> {
    congr
  }

lemma charMatrix_minor_calculation {k : ℕ} (w : Fin (k + 1) → ℂ) :
    let A := charMatrix (n := k + 2) w (k + 2)
    let Minor := A.submatrix Fin.castSucc (Fin.succAbove ⟨k, by omega⟩)
    Minor.det = -Polynomial.C (w ⟨k, by omega⟩) *
                (charMatrix (n := k + 1) (fun i => w (Fin.castSucc i)) k).det := by
  intro A Minor
  rw [Matrix.det_succ_column _ (Fin.last k)]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_last]
  have h_sum_zero : ∑ i : Fin k,
      (-1 : Polynomial ℂ) ^ (↑(Fin.castSucc i) + k) * Minor (Fin.castSucc i) (Fin.last k) *
      (Minor.submatrix (Fin.succAbove (Fin.castSucc i)) (Fin.succAbove (Fin.last k))).det = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have h_col_zero : Minor (Fin.castSucc i) (Fin.last k) = 0 :=
      charMatrix_minor_col_zero w i
    rw [h_col_zero]
    simp
  rw [h_sum_zero]
  rw [zero_add]
  have h_sign : (-1 : Polynomial ℂ) ^ (k + k) = 1 := by
    rw [← two_mul, pow_mul, neg_one_sq, one_pow]
  rw [h_sign, one_mul]
  have h_corner : Minor (Fin.last k) (Fin.last k) = -Polynomial.C (w ⟨k, by omega⟩) :=
    charMatrix_minor_corner w
  rw [h_corner]
  have h_idx : Fin.succAbove (Fin.last k) = Fin.castSucc := by
    ext i
    simp [Fin.succAbove, Fin.lt_def, Fin.castSucc, Fin.last]
  rw [h_idx]
  have h_sub : Minor.submatrix Fin.castSucc Fin.castSucc =
      charMatrix (n := k + 1) (fun i => w i.castSucc) k :=
    charMatrix_minor_sub w
  rw [h_sub]

lemma charMatrix_last_row_zero {k : ℕ} (w : Fin (k + 1) → ℂ) (j : Fin k) :
    charMatrix (n := k + 2) w (k + 2) (Fin.last (k + 1)) (Fin.castSucc (Fin.castSucc j)) = 0 := by
  apply charMatrix_far (n := k + 2)
  simp only [Fin.val_last, Fin.val_castSucc]
  have hj : j.val < k := j.is_lt
  constructor
  · omega
  · constructor <;> omega

lemma charMatrix_trunc (k : ℕ) (w : Fin (k + 1) → ℂ) :
  charMatrix (n := k + 1) (fun i : Fin k => w i.castSucc) k =
  charMatrix (n := k) (fun i : Fin (k - 1) => w (i.castLE (by omega))) k := by
  classical
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [charMatrix_diag]
  · by_cases hsuper : j.val = i.val + 1
    · have hk₁ : i.val < (k + 1) - 1 := by
        simp [i.is_lt]
      have hk₂ : i.val < k - 1 := by
        have hj_lt : j.val < k := j.is_lt
        have : i.val + 1 < k := by simpa [hsuper] using hj_lt
        omega
      have hL :=
        charMatrix_super
          (n := k + 1)
          (w := fun i : Fin k => w i.castSucc)
          (k := k) (i := i) (j := j) hsuper hk₁
      have hR :=
        charMatrix_super
          (n := k)
          (w := fun i : Fin (k - 1) => w (i.castLE (by omega)))
          (k := k) (i := i) (j := j) hsuper hk₂
      have hidx :
        (Fin.castSucc (⟨i.val, hk₁⟩ : Fin k) : Fin (k + 1)) =
        (Fin.castLE (by omega) (⟨i.val, hk₂⟩ : Fin (k - 1))) := by
        apply Fin.ext
        simp
      have hw : w (Fin.castSucc (⟨i.val, hk₁⟩ : Fin k)) =
                w (Fin.castLE (by omega) (⟨i.val, hk₂⟩ : Fin (k - 1))) :=
        congrArg w hidx
      simp [hL, hR, hw]
    · by_cases hsub : i.val = j.val + 1
      · have hk₁ : j.val < (k + 1) - 1 := by
          simp [j.is_lt]
        have hk₂ : j.val < k - 1 := by
          have hi_lt : i.val < k := i.is_lt
          have : j.val + 1 < k := by simpa [hsub] using hi_lt
          omega
        have hL :=
          charMatrix_sub
            (n := k + 1)
            (w := fun i : Fin k => w i.castSucc)
            (k := k) (i := i) (j := j) hsub hk₁
        have hR :=
          charMatrix_sub
            (n := k)
            (w := fun i : Fin (k - 1) => w (i.castLE (by omega)))
            (k := k) (i := i) (j := j) hsub hk₂
        have hidx :
          (Fin.castSucc (⟨j.val, hk₁⟩ : Fin k) : Fin (k + 1)) =
          (Fin.castLE (by omega) (⟨j.val, hk₂⟩ : Fin (k - 1))) := by
          apply Fin.ext
          simp
        have hw : w (Fin.castSucc (⟨j.val, hk₁⟩ : Fin k)) =
                  w (Fin.castLE (by omega) (⟨j.val, hk₂⟩ : Fin (k - 1))) :=
          congrArg w hidx
        simp [hL, hR, hw]
      · have hfar :
          i.val ≠ j.val ∧ i.val ≠ j.val + 1 ∧ j.val ≠ i.val + 1 := by
            refine ⟨?h0, ?h1, ?h2⟩
            · intro hv; apply hij; exact Fin.ext hv
            · intro hv; exact hsub hv
            · intro hv; exact hsuper hv
        have hL :=
          charMatrix_far
            (n := k + 1)
            (w := fun i : Fin k => w i.castSucc)
            (k := k) (i := i) (j := j) hfar
        have hR :=
          charMatrix_far
            (n := k)
            (w := fun i : Fin (k - 1) => w (i.castLE (by omega)))
            (k := k) (i := i) (j := j) hfar
        simp [hL, hR]

lemma charMatrix_det_trunc (k : ℕ) (w : Fin (k + 1) → ℂ) :
  (charMatrix (n := k + 1) (fun i : Fin k => w i.castSucc) k).det =
  (charMatrix (n := k) (fun i : Fin (k - 1) => w (i.castLE (by omega))) k).det := by
  have h := congrArg Matrix.det (charMatrix_trunc (k := k) (w := w))
  simpa using h

lemma charMatrix_last_row_penultimate {k : ℕ} (w : Fin (k + 1) → ℂ) :
    charMatrix (n := k + 2) w (k + 2) (Fin.last (k + 1)) (Fin.castSucc (Fin.last k)) =
    -Polynomial.C (star (w ⟨k, by omega⟩)) := by
  apply charMatrix_sub (n := k + 2)
  · simp only [Fin.val_last, Fin.val_castSucc]

lemma charMatrix_last_row_last {k : ℕ} (w : Fin (k + 1) → ℂ) :
    charMatrix (n := k + 2) w (k + 2) (Fin.last (k + 1)) (Fin.last (k + 1)) = Polynomial.X := by
  apply charMatrix_diag (n := k + 2)

lemma charMatrix_det_recurrence (k : ℕ) (w : Fin (k + 1) → ℂ) :
    (charMatrix (n := k + 2) w (k + 2)).det =
      Polynomial.X * (charMatrix (n := k + 1) (fun i => w (Fin.castSucc i)) (k + 1)).det -
      Polynomial.C (Complex.normSq (w ⟨k, by omega⟩) : ℂ) *
      (charMatrix (n := k) (fun (i : Fin (k - 1)) => w (i.castLE (by omega))) k).det := by
  set A := charMatrix (n := k + 2) w (k + 2) with hA
  have h := Matrix.det_succ_row A (Fin.last (k +  1))
  rw [h]
  rw [Fin.sum_univ_castSucc]
  rw [Fin.sum_univ_castSucc]
  have h_zeros : ∑ x : Fin k,
      (-1 : Polynomial ℂ) ^ ((Fin.last (k + 1)) + (Fin.castSucc (Fin.castSucc x))).val *
      A (Fin.last (k + 1)) (Fin.castSucc (Fin.castSucc x)) *
      (A.submatrix Fin.castSucc (Fin.succAbove (Fin.castSucc (Fin.castSucc x)))).det = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    have h_zero : A (Fin.last (k + 1)) (Fin.castSucc (Fin.castSucc x)) = 0 := by
      rw [hA]
      apply charMatrix_last_row_zero w x
    simp [h_zero]
  simp only [hA, charMatrix_last_row_zero, mul_zero]
  simp only [zero_mul, Finset.sum_const_zero, zero_add]
  rw [Fin.succAbove_last, charMatrix_last_row_penultimate, charMatrix_last_row_last,
      charMatrix_submatrix_cast]
  simp only [pow_add, mul_neg]
  ring_nf
  rw [show (Fin.last k).castSucc.succAbove = Fin.succAbove ⟨k, by omega⟩ by rfl]
  rw [charMatrix_minor_calculation]
  simp [pow_add, Complex.normSq_eq_conj_mul_self]; ring_nf
  rw [mul_comm k 2, pow_mul, neg_one_sq, one_pow, mul_one]
  have hdet := charMatrix_det_trunc (k := k) (w := w)
  simp [hdet]

lemma charMatrix_eq_poly_aux (w : Fin (n - 1) → ℂ) (k : ℕ) (hk : k ≤ n) :
    (charMatrix (fun i => w (i.castLE (Nat.sub_le_sub_right hk 1))) k).det =
    tridiagonalCharPoly w k := by
  revert hk
  induction k using Nat.twoStepInduction with
  | zero =>
    intro hk
    simp [tridiagonalCharPoly]
  | one =>
    intro hk
    simp [tridiagonalCharPoly, charMatrix, tridiagonalMatrix]
  | more k IH1 IH2 =>
    intro hk
    have hk2 : k + 2 ≤ n := hk
    have hk1 : k + 1 ≤ n := by omega
    have hk0 : k ≤ n := by omega
    have h_lt : k < n - 1 := by omega
    erw [charMatrix_det_recurrence k (fun i => w (i.castLE (Nat.sub_le_sub_right hk2 1)))]
    erw [IH2 hk1]
    erw [IH1 hk0]
    simp [tridiagonalCharPoly, h_lt]

lemma charpoly_tridiagonal (w : Fin (n - 1) → ℂ) :
    Matrix.charpoly (tridiagonalMatrix w n) = tridiagonalCharPoly w n := by
  unfold Matrix.charpoly
  rw [← charMatrix_eq_poly_aux w n (le_refl n)]
  congr
  ext i j
  simp only [charMatrix]
  congr
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.map_apply, tridiagonalMatrix]
  split_ifs <;> simp_all

lemma crabb_weights_equality (n : ℕ) :
    let w := fun i => (crabbWeight n i) / 2
    tridiagonalMatrix w n = hermitianPart n := by
  exact (hermitianPart_eq_tridiagonal n).symm

lemma char_poly_recurrence (n : ℕ) (_hn : n ≥ 2) :
    let H := hermitianPart n
    let p := tridiagonalCharPoly (fun i => (crabbWeight n i) / 2)
    p n = Matrix.charpoly H := by 
  intro H p
  simp only [p, H]
  have h_tri : hermitianPart n = tridiagonalMatrix (fun i => (crabbWeight n i) / 2) n := 
    hermitianPart_eq_tridiagonal n
  rw [h_tri]
  rw [charpoly_tridiagonal]

end TridiagonalRecurrence

section SpectralBound

open scoped BigOperators
open Matrix Polynomial Complex

variable {n : ℕ}

noncomputable def hermitianWeights (n : ℕ) (i : Fin (n - 1)) : ℂ :=
  (crabbWeight n i) / 2

lemma hermitianWeights_sq_norm_boundary (hn : n > 2) :
    let w := hermitianWeights n
    Complex.normSq (w ⟨0, by omega⟩) = 1/2 ∧
    Complex.normSq (w ⟨n - 2, by omega⟩) = 1/2 := by
  intro w
  have h_neq : 0 ≠ n - 2 := by omega
  dsimp [w, hermitianWeights, crabbWeight]
  constructor
  · rw [if_neg h_neq]
    simp only [mul_one, map_div₀, Complex.normSq_ofNat]
    rw [Complex.normSq_ofReal]
    rw [← pow_two, Real.sq_sqrt (by norm_num)]
    norm_num
  · rw [if_neg h_neq.symm, if_pos rfl]
    simp only [one_mul, map_div₀, Complex.normSq_ofNat]
    rw [Complex.normSq_ofReal]
    rw [← pow_two, Real.sq_sqrt (by norm_num)]
    norm_num

lemma hermitianWeights_sq_norm_interior (_hn : n ≥ 4) (i : Fin (n - 1))
    (h_first : i.val ≠ 0) (h_last : i.val ≠ n - 2) :
    Complex.normSq (hermitianWeights n i) = 1/4 := by
  unfold hermitianWeights crabbWeight
  simp only [normSq_div, normSq_ofNat]
  rw [if_neg h_first, if_neg h_last]
  simp
  ring

noncomputable def T_poly : ℕ → Polynomial ℂ
  | 0 => 1
  | 1 => X
  | k + 2 => 2 * X * T_poly (k + 1) - T_poly k

lemma T_poly_val_one (k : ℕ) : (T_poly k).eval 1 = 1 := by
  induction k using Nat.twoStepInduction with
  | zero => simp [T_poly]
  | one => simp [T_poly]
  | more k IH1 IH2 =>
    simp [T_poly, IH1, IH2]
    ring


lemma T_poly_pos_mono {x : ℝ} (hx : x > 1) (k : ℕ) :
    0 < ((T_poly k).eval (x : ℂ)).re ∧
    ((T_poly k).eval (x : ℂ)).re < ((T_poly (k + 1)).eval (x : ℂ)).re := by
  induction k using Nat.twoStepInduction with
  | zero =>
    simp only [T_poly, eval_one, eval_X, Complex.one_re, Complex.ofReal_re]
    constructor
    · norm_num
    · exact hx
  | one =>
    simp only [T_poly, eval_sub, eval_mul, eval_X, 
               eval_one, Polynomial.eval_ofNat]
    simp only [Complex.sub_re, Complex.mul_re,
               Complex.ofReal_re, Complex.ofReal_im,
               Complex.one_re, mul_zero, sub_zero]
    norm_num
    constructor
    · linarith
    · nlinarith
  | more k IH1 IH2 =>
    rcases IH1 with ⟨_, hTk_mono⟩
    rcases IH2 with ⟨hTk1_pos, hTk1_mono⟩
    let Tk := ((T_poly k).eval (x : ℂ)).re
    let Tk1 := ((T_poly (k + 1)).eval (x : ℂ)).re
    let Tk2 := ((T_poly (k + 2)).eval (x : ℂ)).re
    let Tk3 := ((T_poly (k + 3)).eval (x : ℂ)).re
    constructor
    · exact hTk1_mono.trans' hTk1_pos
    · have h_recur : Tk3 = 2 * x * Tk2 - Tk1 := by
        dsimp [Tk3, Tk2, Tk1]
        simp only [T_poly, eval_sub, eval_mul, eval_X, Polynomial.eval_ofNat,
                   Complex.sub_re, Complex.mul_re, 
                   Complex.ofReal_re, Complex.ofReal_im, 
                   mul_zero, sub_zero]
        norm_num
      change Tk2 < Tk3
      rw [h_recur]
      have h_helper : Tk1 < (2 * x - 1) * Tk2 := calc
        Tk1 < Tk2 := hTk1_mono
        _   = 1 * Tk2 := by simp
        _   < (2 * x - 1) * Tk2 := by
              apply mul_lt_mul_of_pos_right
              · linarith [hx] 
              · exact hTk1_pos.trans hTk1_mono 
      linarith [h_helper]

lemma T_poly_mono_gt_one {x : ℝ} (hx : x > 1) (k : ℕ) :
    ((T_poly (k + 1)).eval (x : ℂ)).re > ((T_poly k).eval (x : ℂ)).re :=
  (T_poly_pos_mono hx k).2

noncomputable def U_poly : ℕ → Polynomial ℂ
  | 0 => 1
  | 1 => 2 * Polynomial.X
  | k + 2 => 2 * Polynomial.X * U_poly (k + 1) - U_poly k

lemma const_factor (j : ℕ) : 
    C (1 / 2 : ℂ) * C (1 / 2 : ℂ) ^ j = C (1 / 2 : ℂ) ^ j * C (1 / 4 : ℂ) * 2 := by
  rw [mul_assoc]
  change _ = _ * (C (1 / 4) * C 2)
  rw [← map_mul]
  norm_num
  apply mul_comm

lemma half_pow_step (j : ℕ) :
    (1 / 2 : ℂ)^(j+1) = (1 / 2 : ℂ)^j * (1 / 4 : ℂ) * 2 := by
  field_simp
  ring_nf

lemma charPoly_eq_chebyshev_bulk_C {k : ℕ} (hk : 1 ≤ k) :
    let w : Fin (k - 1) → ℂ := fun _ => (1 / 2 : ℂ)
    tridiagonalCharPoly w k
      = Polynomial.C ((1 / 2 : ℂ)^k) * U_poly k := by
  intro w
  suffices ∀ m, m ≤ k → tridiagonalCharPoly w m = Polynomial.C ((1 / 2 : ℂ)^m) * U_poly m from
    this k (le_refl k)
  intro m hm
  induction m using Nat.twoStepInduction with
  | zero =>
    simp only [tridiagonalCharPoly, U_poly, pow_zero, map_one, mul_one]
  | one =>
    simp only [tridiagonalCharPoly, U_poly, pow_one]
    apply Polynomial.ext
    intro n
    simp
  | more j IH1 IH2 =>
      have hj : j < k - 1 := by omega
      have h_le1 : j + 1 ≤ k := by omega
      have h_le2 : j ≤ k := by omega
      have hnorm : (Complex.normSq (w ⟨j, hj⟩) : ℂ) = (1 / 4 : ℂ) := by
        norm_num [w]
      have h_const :
          Polynomial.C ((1 / 2 : ℂ)^j) * Polynomial.C (1 / 4 : ℂ) =
            Polynomial.C ((1 / 2 : ℂ)^(j + 2)) := by
        calc
          Polynomial.C ((1 / 2 : ℂ)^j) * Polynomial.C (1 / 4 : ℂ)
              = Polynomial.C ((1 / 2 : ℂ)^j * (1 / 4 : ℂ)) := by
                  rw [← Polynomial.C_mul]
          _ = Polynomial.C ((1 / 2 : ℂ)^j * (1 / 2 : ℂ)^2) := by
                  norm_num
          _ = Polynomial.C ((1 / 2 : ℂ)^(j + 2)) := by
                  simp [pow_add]
      have hCmul :
          Polynomial.C ((1 / 2 : ℂ)^j * (1 / 2 : ℂ)) =
            Polynomial.C ((1 / 2 : ℂ)^j) * Polynomial.C (1 / 2 : ℂ) := by
        rw [← C_mul]
      have h_powSucc :
          Polynomial.C ((1 / 2 : ℂ)^(j + 1)) =
            Polynomial.C ((1 / 2 : ℂ)^j) * Polynomial.C (1 / 2 : ℂ) := by
        simp [pow_succ]
      have h_inner :
          Polynomial.X * Polynomial.C (1 / 2 : ℂ) * U_poly (j + 1) -
              Polynomial.C (1 / 4 : ℂ) * U_poly j
            =
            Polynomial.C (1 / 4 : ℂ) *
              (2 * Polynomial.X * U_poly (j + 1) - U_poly j) := by
        have h_half :
            (Polynomial.C (1 / 2 : ℂ) : Polynomial ℂ) =
              Polynomial.C (1 / 4 : ℂ) * (2 : Polynomial ℂ) := by
          have hC2 : (Polynomial.C (2 : ℂ) : Polynomial ℂ) = (2 : Polynomial ℂ) := rfl
          calc
            (Polynomial.C (1 / 2 : ℂ) : Polynomial ℂ)
                = Polynomial.C ((1 / 4 : ℂ) * 2) := by norm_num
            _ = Polynomial.C (1 / 4 : ℂ) * (2 : Polynomial ℂ) := by
                  simp [C_mul, hC2]
        calc
          Polynomial.X * Polynomial.C (1 / 2 : ℂ) * U_poly (j + 1) -
              Polynomial.C (1 / 4 : ℂ) * U_poly j
              = Polynomial.C (1 / 2 : ℂ) * Polynomial.X * U_poly (j + 1) -
                  Polynomial.C (1 / 4 : ℂ) * U_poly j := by ring
          _ = (Polynomial.C (1 / 4 : ℂ) * (2 : Polynomial ℂ)) *
                  Polynomial.X * U_poly (j + 1) -
                  Polynomial.C (1 / 4 : ℂ) * U_poly j := by
                rw [h_half]
          _ = Polynomial.C (1 / 4 : ℂ) *
                (2 * Polynomial.X * U_poly (j + 1) - U_poly j) := by
                ring
      calc
        tridiagonalCharPoly w (j + 2)
            = Polynomial.X * tridiagonalCharPoly w (j + 1) -
                Polynomial.C (1 / 4 : ℂ) * tridiagonalCharPoly w j := by
              simp [tridiagonalCharPoly, hj, hnorm]
        _ =
            Polynomial.X * (Polynomial.C ((1 / 2 : ℂ)^(j + 1)) * U_poly (j + 1)) -
              Polynomial.C (1 / 4 : ℂ) * (Polynomial.C ((1 / 2 : ℂ)^j) * U_poly j) := by
              simp [IH2 h_le1, IH1 h_le2]
        _ =
            Polynomial.X * (Polynomial.C ((1 / 2 : ℂ)^j) * Polynomial.C (1 / 2 : ℂ) * U_poly (j + 1)) -
              Polynomial.C (1 / 4 : ℂ) * (Polynomial.C ((1 / 2 : ℂ)^j) * U_poly j) := by
              rw [h_powSucc]
        _ =
            Polynomial.C ((1 / 2 : ℂ)^j) *
              (Polynomial.X * Polynomial.C (1 / 2 : ℂ) * U_poly (j + 1) -
                Polynomial.C (1 / 4 : ℂ) * U_poly j) := by
              ring
        _ =
            Polynomial.C ((1 / 2 : ℂ)^j) *
              (Polynomial.C (1 / 4 : ℂ) *
                (2 * Polynomial.X * U_poly (j + 1) - U_poly j)) := by
              rw [h_inner]
        _ =
            Polynomial.C ((1 / 2 : ℂ)^j) * Polynomial.C (1 / 4 : ℂ) *
              (2 * Polynomial.X * U_poly (j + 1) - U_poly j) := by
              ring
        _ =
            Polynomial.C ((1 / 2 : ℂ)^(j + 2)) *
              (2 * Polynomial.X * U_poly (j + 1) - U_poly j) := by
              rw [h_const]
        _ = Polynomial.C ((1 / 2 : ℂ)^(j + 2)) * U_poly (j + 2) := by
              simp [U_poly]

lemma charPoly_eq_chebyshev_bulk_smul {k : ℕ} (hk : 1 ≤ k) :
    let w : Fin (k - 1) → ℂ := fun _ => (1 / 2 : ℂ)
    tridiagonalCharPoly w k
      = ((1 / 2 : ℂ)^k) • U_poly k := by
  intro w
  simpa [w, smul_eq_C_mul] using (charPoly_eq_chebyshev_bulk_C (k := k) hk)

section QuickWinLemmas

lemma re_le_norm' (z : ℂ) : z.re ≤ ‖z‖ := by
  have h := Complex.abs_re_le_norm z
  exact (abs_le.mp h).2

lemma re_inner_le_opNorm_of_unit {A : E →L[ℂ] E} {x : E} (hx : ‖x‖ = 1) :
    Complex.re ⟪A x, x⟫ ≤ ‖A‖ := by
  have hz : ⟪A x, x⟫ ∈ numericalRange A :=
    mem_numericalRange_of_unit (A := A) (x := x) hx
  have hnorm := norm_le_opNorm_of_mem_numericalRange (A := A) (z := ⟪A x, x⟫) hz
  exact (re_le_norm' _).trans hnorm

lemma re_inner_le_opNorm_mul_norm_sq {A : E →L[ℂ] E} {x : E} :
    Complex.re ⟪A x, x⟫ ≤ ‖A‖ * ‖x‖^2 := by
  have h1 : Complex.re ⟪A x, x⟫ ≤ ‖⟪A x, x⟫‖ := re_le_norm' _
  have h2 : ‖⟪A x, x⟫‖ ≤ ‖A x‖ * ‖x‖ := norm_inner_le_norm (A x) x
  have h3 : ‖A x‖ ≤ ‖A‖ * ‖x‖ := A.le_opNorm x
  have hx : 0 ≤ ‖x‖ := norm_nonneg x
  calc
    Complex.re ⟪A x, x⟫ ≤ ‖A x‖ * ‖x‖ := h1.trans h2
    _ ≤ (‖A‖ * ‖x‖) * ‖x‖ := by exact mul_le_mul_of_nonneg_right h3 hx
    _ = ‖A‖ * ‖x‖^2 := by ring

lemma nontrivial_clm (n : ℕ) (hn : 0 < n) : Nontrivial (Euc n →L[ℂ] Euc n) := by
  classical
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  haveI : Nontrivial (Euc n) := inferInstance
  let e : Euc n := PiLp.basisFun 2 ℂ (Fin n) ⟨0, hn⟩
  have he : e ≠ 0 := by
    intro h
    have h0 := congrArg (fun v => v ⟨0, hn⟩) h
    simp [e] at h0
  refine ⟨⟨(ContinuousLinearMap.id ℂ (Euc n)),
            (0 : Euc n →L[ℂ] Euc n), ?_⟩⟩
  intro h_eq
  have h_apply := congrArg (fun f => f e) h_eq
  have : e = (0 : Euc n) := by simpa using h_apply
  exact he this

lemma hermitianCLM_adjoint_eq (n : ℕ) :
    (hermitianCLM n).adjoint = hermitianCLM n := by
  classical
  refine ContinuousLinearMap.ext fun x => ?_
  refine ext_inner_right (𝕜 := ℂ) (E := Euc n) ?_
  intro y
  calc
    ⟪(hermitianCLM n).adjoint x, y⟫ =
        ⟪x, hermitianCLM n y⟫ :=
          ContinuousLinearMap.adjoint_inner_left (hermitianCLM n) y x
    _ = ⟪hermitianCLM n x, y⟫ :=
        (hermitianCLM_self_adjoint (n := n) (x := x) (y := y)).symm

lemma hermitianCLM_im_zero (n : ℕ) (x : Euc n) :
    Complex.im ⟪hermitianCLM n x, x⟫ = 0 := by
  have h_self : (hermitianCLM n).adjoint = hermitianCLM n :=
    hermitianCLM_adjoint_eq (n := n)
  exact quadratic_form_self_adjoint_real (A := hermitianCLM n) (hA := h_self) x

lemma hermitianCLM_inner_real (n : ℕ) (x : Euc n) :
    ⟪hermitianCLM n x, x⟫ =
      Complex.ofReal (Complex.re ⟪hermitianCLM n x, x⟫) := by
  have h_im := hermitianCLM_im_zero (n := n) (x := x)
  apply Complex.ext
  · simp
  · simp [h_im]

lemma hermitianCLM_numRange_mem (n : ℕ) {x : Euc n} (hx : ‖x‖ = 1) :
    ⟪hermitianCLM n x, x⟫ ∈ numericalRange (hermitianCLM n) :=
  mem_numericalRange_of_unit (A := hermitianCLM n) (x := x) hx

lemma re_inner_hermitianCLM_le_opNorm (n : ℕ) {x : Euc n} (hx : ‖x‖ = 1) :
    Complex.re ⟪hermitianCLM n x, x⟫ ≤ ‖hermitianCLM n‖ :=
  re_inner_le_opNorm_of_unit (A := hermitianCLM n) (x := x) hx

lemma re_inner_hermitianCLM_le_opNorm_sq (n : ℕ) (x : Euc n) :
    Complex.re ⟪hermitianCLM n x, x⟫ ≤ ‖hermitianCLM n‖ * ‖x‖^2 :=
  re_inner_le_opNorm_mul_norm_sq (A := hermitianCLM n) (x := x)

lemma opNorm_hermitianCLM_le_avg (n : ℕ) (_hn : 0 < n) :
    ‖hermitianCLM n‖ ≤ (‖crabbCLM n‖ + ‖(crabbCLM n).adjoint‖) / 2 := by
  classical
  haveI : Nonempty (Fin n) := ⟨⟨0, _hn⟩⟩
  haveI : Nontrivial (Euc n) := by
    classical
    infer_instance
  haveI : Nontrivial (Euc n →L[ℂ] Euc n) := nontrivial_clm n _hn
  have h_add := ContinuousLinearMap.opNorm_add_le (crabbCLM n) (crabbCLM n).adjoint
  have h_smul :=
    ContinuousLinearMap.opNorm_smul_le (c := (1 / 2 : ℂ))
      (crabbCLM n + (crabbCLM n).adjoint)
  calc
    ‖hermitianCLM n‖ =
        ‖(1 / 2 : ℂ) • (crabbCLM n + (crabbCLM n).adjoint)‖ := by rfl
    _ ≤ ‖(1 / 2 : ℂ)‖ * ‖crabbCLM n + (crabbCLM n).adjoint‖ := by
          simpa using h_smul
    _ ≤ ‖(1 / 2 : ℂ)‖ * (‖crabbCLM n‖ + ‖(crabbCLM n).adjoint‖) := by
          have h_nonneg : 0 ≤ ‖(1 / 2 : ℂ)‖ := norm_nonneg _
          exact mul_le_mul_of_nonneg_left h_add h_nonneg
    _ = (1 / 2) * (‖crabbCLM n‖ + ‖(crabbCLM n).adjoint‖) := by
          norm_num
    _ = (‖crabbCLM n‖ + ‖(crabbCLM n).adjoint‖) / 2 := by ring

lemma re_inner_le_one_of_opNorm_le {A : E →L[ℂ] E} {x : E} (hx : ‖x‖ = 1)
    (hA : ‖A‖ ≤ (1 : ℝ)) :
    Complex.re ⟪A x, x⟫ ≤ 1 :=
  (re_inner_le_opNorm_of_unit (A := A) (x := x) hx).trans hA

lemma re_inner_hermitianCLM_le_one
    (n : ℕ) {x : Euc n} (hx : ‖x‖ = 1) (hA : ‖hermitianCLM n‖ ≤ (1 : ℝ)) :
    Complex.re ⟪hermitianCLM n x, x⟫ ≤ 1 :=
  re_inner_le_one_of_opNorm_le (A := hermitianCLM n) (x := x) hx hA

noncomputable def h_eig_vec (n : ℕ) : Fin n → ℝ :=
  fun i => if i.val = 0 ∨ i.val = n - 1 then 1/2 else 1/Real.sqrt 2

lemma h_eig_vec_pos (_hn : n ≥ 2) (i : Fin n) : 0 < h_eig_vec n i := by
  unfold h_eig_vec
  split_ifs
  · norm_num
  · apply div_pos (by norm_num) (Real.sqrt_pos.mpr (by norm_num))

noncomputable def hRowSum (n : ℕ) (i : Fin n) : ℝ :=
  ∑ j, (hermitianPart n i j).re * h_eig_vec n j

lemma h_eig_vec_boundary_left (hn : n ≥ 2) :
    h_eig_vec n ⟨0, by omega⟩ = 1 / 2 := by
  unfold h_eig_vec
  simp only []
  have h_cond : (0 : ℕ) = 0 ∨ (0 : ℕ) = n - 1 := Or.inl rfl
  simp []

lemma h_eig_vec_boundary_right (hn : n ≥ 2) :
  h_eig_vec n ⟨n - 1, by have := hn; omega⟩ = 1 / 2 := by
  unfold h_eig_vec
  simp

lemma h_eig_vec_interior (_hn : n ≥ 2) (i : Fin n)
    (h0 : (i : ℕ) ≠ 0) (hLast : (i : ℕ) ≠ n - 1) :
  h_eig_vec n i = 1 / Real.sqrt 2 := by
  unfold h_eig_vec
  simp [h0, hLast]

lemma h_eig_vec_boundary_right' (hn : n ≥ 2) :
    h_eig_vec n ⟨n - 1, by omega⟩ = 1 / 2 := by
  unfold h_eig_vec
  simp only []
  have h_cond : n - 1 = 0 ∨ n - 1 = n - 1 := Or.inr rfl
  simp []

lemma h_eig_vec_interior' (_hn : n ≥ 2) (i : Fin n)
    (h_neq_0 : i.val ≠ 0) (h_neq_last : i.val ≠ n - 1) :
    h_eig_vec n i = 1 / Real.sqrt 2 := by
  unfold h_eig_vec
  have h_cond : ¬(i.val = 0 ∨ i.val = n - 1) := by
    push_neg
    exact ⟨h_neq_0, h_neq_last⟩
  rw [if_neg h_cond]

lemma hermitianPart_diag_zero (n : ℕ) (i : Fin n) :
  hermitianPart n i i = 0 := by
  classical
  unfold hermitianPart
  simp [crabbMatrix_diag, Matrix.conjTranspose_apply]

lemma hermitianPart_super_entry (n : ℕ)
    (i : Fin n) (hi : i.val < n - 1) :
  hermitianPart n i ⟨i.val + 1, by omega⟩ =
    (crabbWeight n ⟨i.val, hi⟩) / 2 :=
  hermitianPart_superdiag (n := n) i hi

lemma hermitianPart_sub_entry (n : ℕ)
    (i : Fin n) (hi : i.val < n - 1) :
  hermitianPart n ⟨i.val + 1, by omega⟩ i =
    star ((crabbWeight n ⟨i.val, hi⟩) / 2) :=
  hermitianPart_subdiag (n := n) i hi

lemma row0_sum_eq_single (hn : n ≥ 2) :
    hRowSum n ⟨0, by omega⟩ =
    (hermitianPart n ⟨0, by omega⟩ ⟨1, by omega⟩).re *
    h_eig_vec n ⟨1, by omega⟩ := by
  classical
  let i0 : Fin n := ⟨0, by omega⟩
  let j1 : Fin n := ⟨1, by omega⟩
  unfold hRowSum
  rw [Finset.sum_eq_single j1]
  · intro j _ hj_ne
    by_cases hj0 : j = i0
    · rw [hj0]
      rw [hermitianPart_diag_zero]
      simp
    · have h_far : i0.val + 1 < j.val := by
        simp only [i0, j1] at *
        have h_val_ne_0 : j.val ≠ 0 := fun h => hj0 (Fin.ext h)
        have h_val_ne_1 : j.val ≠ 1 := fun h => hj_ne (Fin.ext h)
        omega
      rw [hermitianPart_far_zero n i0 j (Or.inl h_far)]
      simp
  · simp

lemma row0_single_term_value (hn : n ≥ 2) :
  (hermitianPart n ⟨0, by omega⟩ ⟨1, by omega⟩).re *
    h_eig_vec n ⟨1, by omega⟩ =
  h_eig_vec n ⟨0, by omega⟩ := by
  classical
  let i0 : Fin n := ⟨0, by omega⟩
  let j1 : Fin n := ⟨1, by omega⟩
  rw [h_eig_vec_boundary_left hn]
  have h_mat_entry : hermitianPart n i0 j1 = (crabbWeight n ⟨0, by omega⟩) / 2 := by
    apply hermitianPart_super_entry
  rw [h_mat_entry]
  simp only [Complex.div_re]
  by_cases h2 : n = 2
  · subst h2
    have h_w : crabbWeight 2 ⟨0, by omega⟩ = 2 := by
      unfold crabbWeight
      norm_num
      exact sqrt_two_mul_sqrt_two
    have h_v : h_eig_vec 2 j1 = 1 / 2 := by
      have : j1 = ⟨2 - 1, by omega⟩ := Fin.ext rfl
      rw [this]
      exact h_eig_vec_boundary_right (by norm_num)
    rw [h_w, h_v]
    simp
  · have hn_gt : n > 2 := by omega
    have h_w : crabbWeight n ⟨0, by omega⟩ = Real.sqrt 2 := by
      unfold crabbWeight
      simp only []
      simp []
      have h_neq : 0 ≠ n - 2 := by omega
      simp []
      exact h_neq
    have h_v : h_eig_vec n j1 = 1 / Real.sqrt 2 := by
      apply h_eig_vec_interior hn
      · simp [j1] 
      · simp [j1]; omega 
    rw [h_w, h_v]
    simp only [Complex.ofReal_re]
    field_simp
    norm_num [Complex.normSq, Complex.re, Complex.im, Complex.ofReal_re, Complex.ofReal_im]
    ring

lemma hermitianPart_mul_eig_vec_left (hn : n ≥ 2) :
  hRowSum n ⟨0, by omega⟩ = h_eig_vec n ⟨0, by omega⟩ := by
  have := row0_sum_eq_single (n := n) hn
  simpa [this] using row0_single_term_value (n := n) hn

lemma lastRow_single_term_value (hn : n ≥ 2) :
  (hermitianPart n ⟨n - 1, by omega⟩ ⟨n - 2, by omega⟩).re *
    h_eig_vec n ⟨n - 2, by omega⟩ =
  h_eig_vec n ⟨n - 1, by omega⟩ := by
  classical
  let i_last : Fin n := ⟨n - 1, by omega⟩
  let j_prev : Fin n := ⟨n - 2, by omega⟩
  rw [h_eig_vec_boundary_right hn]
  have h_lt : j_prev.val < n - 1 := by simp [j_prev]; omega
  have h_mat : hermitianPart n i_last j_prev = star ((crabbWeight n ⟨j_prev.val, h_lt⟩) / 2) := by
    convert hermitianPart_sub_entry n j_prev h_lt using 2
    · apply Fin.ext
      simp [i_last, j_prev]
      omega
  rw [h_mat]
  simp only [Complex.star_def, Complex.div_re, Complex.conj_re]
  by_cases h2 : n = 2
  · subst h2
    have h_w : crabbWeight 2 ⟨0, by omega⟩ = 2 := by
      unfold crabbWeight; norm_num; exact sqrt_two_mul_sqrt_two
    have h_v : h_eig_vec 2 ⟨0, by omega⟩ = 1 / 2 := by
       exact h_eig_vec_boundary_left (by norm_num)
    have : j_prev = ⟨0, by omega⟩ := Fin.ext rfl
    simp [this] at h_w h_v ⊢
    rw [h_w, h_v]
    simp
  · have hn_gt : n > 2 := by omega
    have h_w : crabbWeight n ⟨j_prev.val, h_lt⟩ = Real.sqrt 2 := by
      unfold crabbWeight
      simp only []
      have h_j_val : ↑j_prev = n - 2 := by simp [j_prev]
      rw [if_neg (by omega)]
      rw [if_pos rfl]
      simp
    have h_v : h_eig_vec n j_prev = 1 / Real.sqrt 2 := by
      apply h_eig_vec_interior hn
      · simp [j_prev]; omega
      · simp [j_prev]; omega
    rw [h_w, h_v]
    simp only [Complex.ofReal_re]
    field_simp
    norm_num [Complex.normSq, Complex.ofReal_re, Complex.ofReal_im]
    ring

lemma lastRow_sum_eq_single (hn : n ≥ 2) :
    hRowSum n ⟨n - 1, by omega⟩ =
    (hermitianPart n ⟨n - 1, by omega⟩ ⟨n - 2, by omega⟩).re *
    h_eig_vec n ⟨n - 2, by omega⟩ := by
  classical
  let i_last : Fin n := ⟨n - 1, by omega⟩
  let j_prev : Fin n := ⟨n - 2, by omega⟩
  unfold hRowSum
  rw [Finset.sum_eq_single j_prev]
  · intro j _ hj_ne
    by_cases hj_last : j = i_last
    · rw [hj_last, hermitianPart_diag_zero]; simp
    · have h_far : j.val + 1 < i_last.val := by
        simp [i_last, j_prev] at *
        have : j.val < n - 1 := by 
           have h_lt := j.is_lt
           have h_ne_prev : j.val ≠ n - 2 := fun h => hj_ne (Fin.ext h)
           have h_ne_last : j.val ≠ n - 1 := fun h => hj_last (Fin.ext h)
           omega
        simp
        have h_le : j.val ≤ n - 2 := by omega
        have h_ne : j.val ≠ n - 2 := by
          intro h
          apply hj_ne
          exact Fin.ext h
        have h_lt : j.val < n - 2 := by omega
        omega
      rw [hermitianPart_far_zero n i_last j (Or.inr h_far)]
      simp
  · simp

lemma hermitianPart_mul_eig_vec_right (hn : n ≥ 2) :
  hRowSum n ⟨n - 1, by omega⟩ = h_eig_vec n ⟨n - 1, by omega⟩ := by
  have h_sum := lastRow_sum_eq_single (n := n) hn
  have h_val := lastRow_single_term_value (n := n) hn
  rw [h_sum, h_val]

def prevIndex (i : Fin n) (_h0 : (i : ℕ) ≠ 0) : Fin n :=
  ⟨i.val - 1, by
    have hi := i.is_lt
    omega⟩

def nextIndex (i : Fin n) (hLast : (i : ℕ) ≠ n - 1) : Fin n :=
  ⟨i.val + 1, by
    have hi := i.is_lt
    have : i.val + 1 ≤ n - 1 :=
      by
        have hi' : i.val < n - 1 := by
          have := hi; omega
        exact Nat.succ_le_of_lt hi'
    have h' : i.val + 1 < n := Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hi) ?h_ne
    all_goals omega⟩

lemma interior_indices_distinct (_hn : n ≥ 2) (i : Fin n)
    (h0 : (i : ℕ) ≠ 0) (hLast : (i : ℕ) ≠ n - 1) :
    prevIndex i h0 ≠ nextIndex i hLast := by
  intro h_eq
  simp [prevIndex, nextIndex] at h_eq

lemma interior_entry_zero_of_ne (_hn : n ≥ 2) (i : Fin n)
    (h0 : (i : ℕ) ≠ 0) (hLast : (i : ℕ) ≠ n - 1)
    (j : Fin n)
    (hj_prev : j ≠ prevIndex i h0)
    (hj_next : j ≠ nextIndex i hLast) :
    hermitianPart n i j = 0 := by
  by_cases hij : j = i
  · rw [hij]
    exact hermitianPart_diag_zero n i
  · apply hermitianPart_far_zero
    simp [prevIndex, nextIndex] at hj_prev hj_next
    have h_far : i.val + 1 < j.val ∨ j.val + 1 < i.val := by
      apply Decidable.or_iff_not_imp_left.mpr
      intro h_not_right
      have h1 : i.val + 1 > j.val := by
        by_contra h
        push_neg at h
        have h_le : i.val + 1 ≤ j.val := by omega
        have h_eq : i.val + 1 = j.val := by
          by_cases h_lt : i.val + 1 < j.val
          · have h2 : j = nextIndex i hLast := by
              apply Fin.ext
              simp [nextIndex]
              omega
            contradiction
          · omega
        have h2 : j = ⟨↑i + 1, by omega⟩ := by
          simp [h_eq]
        contradiction
      have h2 : j.val + 1 < i.val := by
        by_contra h
        push_neg at h
        have h_i_le_j1 : i.val ≤ j.val + 1 := by omega
        have h_eq : i.val = j.val + 1 := by omega
        have h3 : j = prevIndex i h0 := by
          simp [prevIndex, h_eq]
        contradiction
      exact h2
    exact h_far

lemma interior_sum_compl_zero (hn : n ≥ 2) (i : Fin n)
    (h0 : (i : ℕ) ≠ 0) (hLast : (i : ℕ) ≠ n - 1)
    (S : Finset (Fin n)) (hS : S = {prevIndex i h0, nextIndex i hLast}) :
    ∑ j ∈ Finset.univ \ S, (hermitianPart n i j).re * h_eig_vec n j = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  rw [hS] at hj
  simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, 
             Finset.mem_singleton, true_and, not_or] at hj
  rw [interior_entry_zero_of_ne hn i h0 hLast j hj.1 hj.2]
  simp

lemma interior_row_prev_entry (hn : n ≥ 2) (i : Fin n)
    (h0 : (i : ℕ) ≠ 0) :
  let j_prev := prevIndex (n := n) i h0
  hermitianPart n i j_prev =
    star (crabbWeight n ⟨j_prev.val, by
      simp [j_prev, prevIndex]
      have hi := i.is_lt
      omega⟩ / 2) := by
  intro j_prev
  have h_bound : j_prev.val < n - 1 := by
    simp [j_prev, prevIndex]
    have := i.is_lt
    omega
  have h_i_eq : i = ⟨j_prev.val + 1, by omega⟩ := by
    apply Fin.ext
    simp [j_prev, prevIndex]
    omega
  conv_lhs => rw [h_i_eq]
  exact hermitianPart_sub_entry n j_prev h_bound

lemma interior_row_next_entry (hn : n ≥ 2) (i : Fin n)
    (hLast : (i : ℕ) ≠ n - 1) :
  let j_next := nextIndex (n := n) i hLast
  hermitianPart n i j_next =
    crabbWeight n ⟨i.val, by
      have hi := i.is_lt
      omega⟩ / 2 := by
  intro j_next
  have h_bound : i.val < n - 1 := by
    have hi := i.is_lt
    omega
  have h_j_eq : j_next = ⟨i.val + 1, by omega⟩ := by
    apply Fin.ext
    simp [j_next, nextIndex]
  rw [h_j_eq]
  exact hermitianPart_super_entry n i h_bound

lemma interior_row_sum_two_terms (hn : n ≥ 2) (i : Fin n)
    (h0 : (i : ℕ) ≠ 0) (hLast : (i : ℕ) ≠ n - 1) :
  hRowSum n i =
    (hermitianPart n i (prevIndex i h0)).re * h_eig_vec n (prevIndex i h0) +
    (hermitianPart n i (nextIndex i hLast)).re * h_eig_vec n (nextIndex i hLast) := by
  classical
  let j_prev := prevIndex i h0
  let j_next := nextIndex i hLast
  let S : Finset (Fin n) := {j_prev, j_next}
  unfold hRowSum
  have h_subset : S ⊆ Finset.univ := Finset.subset_univ S
  rw [← Finset.sum_sdiff h_subset]
  have h_rest_zero :
      ∑ j ∈ Finset.univ \ S, (hermitianPart n i j).re * h_eig_vec n j = 0 := by
    apply interior_sum_compl_zero hn i h0 hLast S rfl
  rw [h_rest_zero]
  have h_ne : j_prev ≠ j_next :=
    interior_indices_distinct hn i h0 hLast
  rw [Finset.sum_pair h_ne]
  simp only [show j_prev = prevIndex i h0 by rfl, show j_next = nextIndex i hLast by rfl]
  ring

lemma val_helper_arithmetic :
    (1 / Real.sqrt 2) * (1 / 2) + (1 / 2) * (1 / Real.sqrt 2) = 1 / Real.sqrt 2 := by
  ring

lemma val_helper_arithmetic_2 :
    (1 / Real.sqrt 2) * (1 / 2) + (1 / Real.sqrt 2) * (1 / 2) = 1 / Real.sqrt 2 := by
  ring

lemma h_eig_vec_prev_entry {n : ℕ} (hn : n ≥ 3) (i : Fin n)
    (h0 : (i : ℕ) ≠ 0) :
    let j := prevIndex i h0
    h_eig_vec n j = if i.val = 1 then 1/2 else 1/Real.sqrt 2 := by
  intro j
  by_cases h1 : i.val = 1
  · have : j.val = 0 := by simp [j, prevIndex, h1]
    rw [show h_eig_vec n j = 1/2 by simp [this, h_eig_vec]]
    simp [h1]
  · have h_boundary : j.val ≠ 0 ∧ j.val ≠ n - 1 := by
      constructor
      · simp [j, prevIndex]; omega
      · simp [j, prevIndex]; omega
    rw [if_neg h1]
    apply h_eig_vec_interior (by omega)
    · exact h_boundary.1
    · exact h_boundary.2

lemma h_eig_vec_next_entry {n : ℕ} (hn : n ≥ 3) (i : Fin n)
    (hLast : (i : ℕ) ≠ n - 1) :
    let j := nextIndex i hLast
    h_eig_vec n j = if i.val = n - 2 then 1/2 else 1/Real.sqrt 2 := by
  intro j
  by_cases h_nm2 : i.val = n - 2
  · have : j.val = n - 1 := by { simp [j, nextIndex, h_nm2]; omega }
    rw [show h_eig_vec n j = 1/2 by simp [this, h_eig_vec]]
    simp [h_nm2]
  · have h_boundary : j.val ≠ 0 ∧ j.val ≠ n - 1 := by
      constructor
      · simp [j, nextIndex]
      · simp [j, nextIndex]; omega
    rw [if_neg h_nm2]
    apply h_eig_vec_interior (by omega)
    · exact h_boundary.1
    · exact h_boundary.2

lemma hermitianPart_re_prev_entry {n : ℕ} (hn : n ≥ 3) (i : Fin n)
    (h0 : (i : ℕ) ≠ 0) (hLast : (i : ℕ) ≠ n - 1) :
    let j := prevIndex i h0
    (hermitianPart n i j).re =
      if i.val = 1 then 1/Real.sqrt 2 else 1/2 := by
  intro j
  have h_entry := interior_row_prev_entry (by omega) i h0
  dsimp [j] at h_entry
  rw [h_entry]
  simp only [Complex.div_re, Complex.conj_re]
  unfold crabbWeight
  by_cases h1 : i.val = 1
  · have h_prev_zero : (prevIndex i h0).val = 0 := by simp [prevIndex, h1]
    rw [if_pos h1]
    simp only [h_prev_zero, ↓reduceIte]
    field_simp
    norm_num [Complex.normSq, Complex.re, 
              Complex.im, Complex.ofReal_re, 
              Complex.ofReal_im]
    ring_nf
    norm_num [show 0 ≠ n - 2 by omega, Complex.ofReal_re, Real.sq_sqrt]
  · rw [if_neg h1]
    have h_prev_nz : (prevIndex i h0).val ≠ 0 := by simp [prevIndex]; omega
    have h_prev_nlast : (prevIndex i h0).val ≠ n - 2 := by
      simp [prevIndex]
      have hi : i.val < n := i.is_lt
      intro h_eq
      have h_i_eq_n1 : ↑i = n - 1 := by omega
      have h_contra : (i : ℕ) = n - 1 := h_i_eq_n1
      exact hLast h_contra
    simp only [h_prev_nz, h_prev_nlast, ↓reduceIte]
    field_simp
    norm_num [Complex.normSq, Complex.ofReal_re, 
              Complex.ofReal_im, show (2 : ℂ).re = 2 by simp, 
              show (2 : ℂ).im = 0 by simp]

lemma hermitianPart_re_next_entry {n : ℕ} (hn : n ≥ 3) (i : Fin n)
    (h0 : (i : ℕ) ≠ 0) (hLast : (i : ℕ) ≠ n - 1) :
    let j := nextIndex i hLast
    (hermitianPart n i j).re =
      if i.val = n - 2 then 1/Real.sqrt 2 else 1/2 := by
  intro j
  have h_entry := interior_row_next_entry (by omega) i hLast
  dsimp [j] at h_entry
  rw [h_entry]
  simp only [Complex.div_re]
  unfold crabbWeight
  by_cases h_nm2 : i.val = n - 2
  · rw [if_pos h_nm2]
    have h_not_zero : i.val ≠ 0 := by
      rw [h_nm2]
      omega
    simp only [h_nm2, ↓reduceIte]
    field_simp
    norm_num [show n - 2 ≠ 0 by omega, Complex.ofReal_re, 
              Complex.ofReal_im, Real.sq_sqrt, 
              pow_two, Complex.normSq]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · rw [if_neg h_nm2]
    have h_not_zero : i.val ≠ 0 := h0
    simp only [h_not_zero, h_nm2, ↓reduceIte]
    field_simp
    norm_num [Complex.normSq, Complex.ofReal_re, Complex.ofReal_im]

lemma hermitianPart_re_next_entry_strict {n : ℕ} (hn : n ≥ 3) (i : Fin n)
    (h0 : (i : ℕ) ≠ 0) (hLast : (i : ℕ) ≠ n - 1) :
    let j := nextIndex i hLast
    (hermitianPart n i j).re =
      if i.val = n - 2 then 1/Real.sqrt 2 else 1/2 := by
  intro j
  have h_entry := interior_row_next_entry (by omega) i hLast
  dsimp [j] at h_entry
  rw [h_entry]
  simp only [Complex.div_re]
  unfold crabbWeight
  by_cases h_nm2 : i.val = n - 2
  · rw [if_pos h_nm2]
    have h_not_zero : i.val ≠ 0 := by
      rw [h_nm2]
      omega
    simp only [h_nm2, ↓reduceIte]
    field_simp
    norm_num [show n - 2 ≠ 0 by omega, Complex.ofReal_re, 
              Complex.ofReal_im, Real.sq_sqrt, 
              pow_two, Complex.normSq]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · rw [if_neg h_nm2]
    simp only [h0, h_nm2, ↓reduceIte]
    field_simp
    norm_num [Complex.normSq, Complex.ofReal_re, Complex.ofReal_im]

lemma calc_term_i_eq_1 {n : ℕ} (hn : n ≥ 3) (i : Fin n)
    (h1 : i.val = 1) (h0 : (i : ℕ) ≠ 0) (hLast : (i : ℕ) ≠ n - 1) :
    (hermitianPart n i (prevIndex i h0)).re * h_eig_vec n (prevIndex i h0) +
    (hermitianPart n i (nextIndex i hLast)).re * h_eig_vec n (nextIndex i hLast) =
    1 / Real.sqrt 2 := by
  rw [hermitianPart_re_prev_entry hn i h0 hLast]
  rw [h_eig_vec_prev_entry hn i h0]
  simp only [h1, if_true]
  rw [hermitianPart_re_next_entry_strict hn i h0 hLast]
  rw [h_eig_vec_next_entry hn i hLast]
  by_cases h_n3 : n = 3
  · subst h_n3
    have h_nm2 : i.val = 3 - 2 := by rw [h1]
    simp only [h_nm2, if_true]
    exact val_helper_arithmetic_2
  · have h_nm2 : i.val ≠ n - 2 := by omega
    simp only [h_nm2, if_false]
    exact val_helper_arithmetic

lemma calc_term_i_eq_nm2 {n : ℕ} (hn : n ≥ 3) (i : Fin n)
    (h_nm2 : i.val = n - 2) (h0 : (i : ℕ) ≠ 0) (hLast : (i : ℕ) ≠ n - 1) :
    (hermitianPart n i (prevIndex i h0)).re * h_eig_vec n (prevIndex i h0) +
    (hermitianPart n i (nextIndex i hLast)).re * h_eig_vec n (nextIndex i hLast) =
    1 / Real.sqrt 2 := by
  rw [hermitianPart_re_next_entry_strict hn i h0 hLast]
  rw [h_eig_vec_next_entry hn i hLast]
  simp only [h_nm2, if_true]
  rw [hermitianPart_re_prev_entry hn i h0 hLast]
  rw [h_eig_vec_prev_entry hn i h0]
  by_cases h_n3 : n = 3
  · subst h_n3
    have h1 : i.val = 1 := by rw [h_nm2]
    simp only [h1, if_true]
    exact val_helper_arithmetic_2
  · have h1 : i.val ≠ 1 := by omega
    simp only [h1, if_false]
    ring_nf

lemma calc_term_mid {n : ℕ} (hn : n ≥ 3) (i : Fin n)
    (h1 : i.val ≠ 1) (h_nm2 : i.val ≠ n - 2)
    (h0 : (i : ℕ) ≠ 0) (hLast : (i : ℕ) ≠ n - 1) :
    (hermitianPart n i (prevIndex i h0)).re * h_eig_vec n (prevIndex i h0) +
    (hermitianPart n i (nextIndex i hLast)).re * h_eig_vec n (nextIndex i hLast) =
    1 / Real.sqrt 2 := by
  rw [hermitianPart_re_prev_entry hn i h0 hLast]
  rw [h_eig_vec_prev_entry hn i h0]
  rw [hermitianPart_re_next_entry_strict hn i h0 hLast]
  rw [h_eig_vec_next_entry hn i hLast]
  simp [h1, h_nm2]
  field_simp; ring

lemma interior_row_two_terms_value (hn : n ≥ 3) (i : Fin n)
    (h0 : (i : ℕ) ≠ 0) (hLast : (i : ℕ) ≠ n - 1) :
  (hermitianPart n i (prevIndex (n := n) i h0)).re *
      h_eig_vec n (prevIndex (n := n) i h0) +
    (hermitianPart n i (nextIndex (n := n) i hLast)).re *
      h_eig_vec n (nextIndex (n := n) i hLast) =
    h_eig_vec n i := by
  rw [h_eig_vec_interior' (by omega) i h0 hLast]
  by_cases h1 : i.val = 1
  · exact calc_term_i_eq_1 hn i h1 h0 hLast
  by_cases h_nm2 : i.val = n - 2
  · exact calc_term_i_eq_nm2 hn i h_nm2 h0 hLast
  · exact calc_term_mid hn i h1 h_nm2 h0 hLast

lemma hermitianPart_mul_eig_vec_interior (hn : n ≥ 3) (i : Fin n)
    (h0 : (i : ℕ) ≠ 0) (hLast : (i : ℕ) ≠ n - 1) :
  hRowSum n i = h_eig_vec n i := by
  classical
  let j_prev := prevIndex i h0
  let j_next := nextIndex i hLast
  let S : Finset (Fin n) := {j_prev, j_next}
  unfold hRowSum
  have h_subset : S ⊆ Finset.univ := Finset.subset_univ S
  rw [← Finset.sum_sdiff h_subset]
  have h_sum_rest_zero :
      ∑ j ∈ Finset.univ \ S, (hermitianPart n i j).re * h_eig_vec n j = 0 := by
    apply interior_sum_compl_zero (by omega) i h0 hLast S rfl
  rw [h_sum_rest_zero, zero_add]
  have h_ne : prevIndex i h0 ≠ nextIndex i hLast :=
    interior_indices_distinct (by omega) i h0 hLast
  rw [Finset.sum_pair h_ne]
  calc
  (hermitianPart n i j_prev).re * h_eig_vec n j_prev + 
    (hermitianPart n i j_next).re * h_eig_vec n j_next = h_eig_vec n i := 
    interior_row_two_terms_value (by omega) i h0 hLast

lemma hermitianPart_mul_eig_vec (hn : n ≥ 2) (i : Fin n) :
    let A := hermitianPart n
    let v := h_eig_vec n
    ∑ j, (A i j).re * v j = v i := by
  intro A v
  by_cases h0 : (i : ℕ) = 0
  · have h_eq : i = ⟨0, by omega⟩ := Fin.ext h0
    rw [h_eq]
    exact hermitianPart_mul_eig_vec_left hn
  · by_cases h_last : (i : ℕ) = n - 1
    · have h_eq : i = ⟨n - 1, by omega⟩ := Fin.ext h_last
      rw [h_eq]
      exact hermitianPart_mul_eig_vec_right hn
    · have hn3 : n ≥ 3 := by
        have hi_lt : (i : ℕ) < n := i.is_lt
        omega
      exact hermitianPart_mul_eig_vec_interior hn3 i h0 h_last

lemma hermitianPart_eigenvector_prop (hn : n ≥ 2) :
    let A := hermitianPart n
    let v := h_eig_vec n
    Matrix.mulVec (A.map Complex.re) v = v := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
  exact hermitianPart_mul_eig_vec hn i

lemma hermitianPart_is_real (n : ℕ) (i j : Fin n) :
    (hermitianPart n i j).im = 0 := by
  have h_weight_real : ∀ k, (crabbWeight n k).im = 0 := by
    intro k
    unfold crabbWeight
    rw [Complex.mul_im]
    repeat split_ifs <;> simp [Complex.ofReal_im]
  have h_crabb_real : ∀ k m, (CrabbMatrix n k m).im = 0 := by
    intro k m
    unfold CrabbMatrix
    split_ifs
    · exact h_weight_real _
    · simp
  unfold hermitianPart
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.conjTranspose_apply, smul_eq_mul]
  rw [Complex.mul_im]
  have h_half_im : (1 / 2 : ℂ).im = 0 := by norm_num
  rw [h_half_im]
  simp only [zero_mul, add_zero]
  rw [Complex.add_im]
  have h1 : (CrabbMatrix n i j).im = 0 := h_crabb_real i j
  have h2 : (star (CrabbMatrix n j i)).im = -(CrabbMatrix n j i).im := by
    simp []
  rw [h2, h1, h_crabb_real]
  all_goals norm_num

lemma hermitianPart_nonneg (n : ℕ) (i j : Fin n) :
    0 ≤ (hermitianPart n i j).re := by
  classical
  rw [hermitianPart_eq_tridiagonal]
  unfold tridiagonalMatrix
  split_ifs with h_super h_sub
  · simp [crabbWeight]
    split_ifs <;> norm_num [Real.sqrt_pos]
    all_goals positivity
  · simp [crabbWeight]
    split_ifs <;> norm_num [Real.sqrt_pos]
    all_goals positivity
  · norm_num

lemma hermitian_of_real_symmetric {n : ℕ} 
    (M : Matrix (Fin n) (Fin n) ℝ) 
    (hM_sym : M.IsSymm) : (M.map Complex.ofReal).IsHermitian := by
  unfold Matrix.IsHermitian Matrix.conjTranspose
  ext i j
  simp
  exact hM_sym.apply i j

lemma lambda_max_is_eigenvalue {n : ℕ} 
    (M : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) 
      (lambda_max : ℝ) (_hM_sym : M.IsSymm) 
      (_hv_pos : ∀ i, 0 < v i) 
      (h_eig : ∀ i, ∑ j, M i j * v j = lambda_max * v i) : 
  (M.map Complex.ofReal).mulVec (fun i => Complex.ofReal (v i)) = 
    Complex.ofReal lambda_max • (fun i => Complex.ofReal (v i)) := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply]
  have h := h_eig i
  simp [← Complex.ofReal_mul, ← Complex.ofReal_sum, h]

lemma weighted_am_gm_sq {x y a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    2 * x * y ≤ (b / a) * x ^ 2 + (a / b) * y ^ 2 := by
  have h_sq : 0 ≤ (Real.sqrt (b / a) * x - Real.sqrt (a / b) * y) ^ 2 := sq_nonneg _
  have h_pos : 0 < a * b := mul_pos ha hb
  have h_div_pos : 0 < b / a := div_pos hb ha
  have h_div_pos' : 0 < a / b := div_pos ha hb
  have h_expanded : (Real.sqrt (b / a) * x - Real.sqrt (a / b) * y) ^ 2 
      = (Real.sqrt (b / a) * x) ^ 2 - 2 * (Real.sqrt (b / a) * x) * (Real.sqrt (a / b) * y) + (Real.sqrt (a / b) * y) ^ 2 := by 
    ring
  rw [h_expanded] at h_sq
  have h1 : (Real.sqrt (b / a) * x) ^ 2 = (b / a) * x ^ 2 := by
    calc 
      (Real.sqrt (b / a) * x) ^ 2 = (Real.sqrt (b / a)) ^ 2 * x ^ 2 := by ring
      _ = (b / a) * x ^ 2 := by rw [Real.sq_sqrt (le_of_lt h_div_pos)]
  have h2 : (Real.sqrt (a / b) * y) ^ 2 = (a / b) * y ^ 2 := by
    calc 
      (Real.sqrt (a / b) * y) ^ 2 = (Real.sqrt (a / b)) ^ 2 * y ^ 2 := by ring
      _ = (a / b) * y ^ 2 := by rw [Real.sq_sqrt (le_of_lt h_div_pos')]
  have h_sq' : 0 ≤ (b / a) * x ^ 2 - 2 * (Real.sqrt (b / a) * x) * (Real.sqrt (a / b) * y) + (a / b) * y ^ 2 := by 
    rw [h1, h2] at h_sq
    exact h_sq
  have h_rearranged : 2 * (Real.sqrt (b / a) * x) * (Real.sqrt (a / b) * y) ≤ (b / a) * x ^ 2 + (a / b) * y ^ 2 := by
    linarith [h_sq']
  have h_simplified : 2 * (Real.sqrt (b / a) * x) * (Real.sqrt (a / b) * y) = 2 * x * y := by
    have h3 : Real.sqrt (b / a) * Real.sqrt (a / b) = 1 := by
      calc
        Real.sqrt (b / a) * Real.sqrt (a / b) = Real.sqrt ((b / a) * (a / b)) := by 
          rw [← Real.sqrt_mul (by positivity)]
        _ = Real.sqrt 1 := by 
          have h_cancel : (b / a) * (a / b) = 1 := by 
            field_simp [h_pos]
          rw [h_cancel]
        _ = 1 := Real.sqrt_one
    calc
      2 * (Real.sqrt (b / a) * x) * (Real.sqrt (a / b) * y) 
          = 2 * (Real.sqrt (b / a) * Real.sqrt (a / b)) * (x * y) := by 
          ring
      _ = 2 * 1 * (x * y) := by 
        rw [h3]
      _ = 2 * x * y := by 
        ring
  linarith [h_rearranged, h_simplified]

lemma matrix_weighted_bound {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ)
    (i j : Fin n) (xi xj : ℝ)
    (hM : 0 ≤ M i j) (hv : ∀ k, 0 < v k) :
    2 * M i j * xi * xj ≤ M i j * (v j / v i) * xi ^ 2 + M i j * (v i / v j) * xj ^ 2 := by
  by_cases h_zero : M i j = 0
  · simp [h_zero]
  · have h_factor : 2 * xi * xj ≤ (v j / v i) * xi ^ 2 + (v i / v j) * xj ^ 2 :=
      weighted_am_gm_sq (hv i) (hv j)
    have h_pos : 0 < M i j := lt_of_le_of_ne hM (Ne.symm h_zero)
    nlinarith

lemma sum_matrix_weighted_split {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (v : Fin n → ℝ) (x : Fin n → ℝ) :
    ∑ i, ∑ j, (M i j * (v j / v i) * (x i)^2) =
    ∑ i, ((x i)^2 / v i) * (∑ j, M i j * v j) := by
  apply Finset.sum_congr rfl
  intro i _
  have h1 : ∑ j, (M i j * (v j / v i) * x i ^ 2)
        = (x i ^ 2 / v i) * (∑ j, M i j * v j) := by
    calc
      ∑ j, (M i j * (v j / v i) * x i ^ 2)
          = ∑ j, ((x i ^ 2 / v i) * (M i j * v j)) := by 
            apply Finset.sum_congr rfl
            intro j _
            field_simp
      _ = (x i ^ 2 / v i) * (∑ j, M i j * v j) := by 
            rw [Finset.mul_sum] 
  simp [h1]

lemma sum_matrix_weighted_swap {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (v : Fin n → ℝ) (x : Fin n → ℝ) (hM_sym : M.IsSymm) :
    ∑ i, ∑ j, (M i j * (v i / v j) * (x j)^2) =
    ∑ i, ∑ j, (M i j * (v j / v i) * (x i)^2) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  rw [← Matrix.IsSymm.apply hM_sym i j]

lemma double_sum_bound_by_eigenvalue {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (v : Fin n → ℝ) (x : Fin n → ℝ) (lambda : ℝ)
    (h_eig : ∀ i, ∑ j, M i j * v j = lambda * v i)
    (hv : ∀ i, 0 < v i) :
    ∑ i, ∑ j, (M i j * (v j / v i) * (x i)^2) = lambda * ∑ i, (x i)^2 := by
  rw [sum_matrix_weighted_split]
  have h1 : ∀ i, x i ^ 2 / v i * ∑ j, M i j * v j = lambda * x i ^ 2 := by
    intro i
    rw [h_eig i]
    field_simp [ne_of_gt (hv i)]
  have h_sum : ∑ i, (x i ^ 2 / v i * ∑ j, M i j * v j) = ∑ i, (lambda * x i ^ 2) := by
    apply Finset.sum_congr rfl
    intro i _
    exact h1 i
  rw [h_sum]
  rw [Finset.mul_sum]

lemma real_quad_form_abs_bound {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (v : Fin n → ℝ) (x : Fin n → ℝ) (lambda : ℝ)
    (hM_sym : M.IsSymm)
    (hM_nonneg : ∀ i j, 0 ≤ M i j)
    (hv_pos : ∀ i, 0 < v i)
    (h_eig : ∀ i, ∑ j, M i j * v j = lambda * v i) :
    ∑ i, ∑ j, M i j * x i * x j ≤ lambda * ∑ i, (x i)^2 := by
  have h_term : ∀ i j, 2 * M i j * x i * x j ≤
      M i j * (v j / v i) * (x i)^2 + M i j * (v i / v j) * (x j)^2 :=
    fun i j => matrix_weighted_bound M v i j (x i) (x j) (hM_nonneg i j) hv_pos
  have h_sum1 : ∑ i, ∑ j, (2 * M i j * x i * x j) = 2 * ∑ i, ∑ j, M i j * x i * x j := by 
    simp [Finset.mul_sum, mul_assoc]
  have h_sum2 : ∑ i, ∑ j, (2 * M i j * x i * x j) ≤
      ∑ i, ∑ j, (M i j * (v j / v i) * (x i)^2 + M i j * (v i / v j) * (x j)^2) := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    exact h_term i j
  have h_sum3 : 2 * ∑ i, ∑ j, M i j * x i * x j ≤
      ∑ i, ∑ j, (M i j * (v j / v i) * (x i)^2 + M i j * (v i / v j) * (x j)^2) := by 
    linarith [h_sum1, h_sum2]
  have h_sum4 : ∑ i, ∑ j, (M i j * (v j / v i) * (x i)^2 + M i j * (v i / v j) * (x j)^2) =
      ∑ i, ∑ j, M i j * (v j / v i) * (x i)^2 + ∑ i, ∑ j, M i j * (v i / v j) * (x j)^2 := by
    simp [Finset.sum_add_distrib]
  have h_sum5 : 2 * ∑ i, ∑ j, M i j * x i * x j ≤
      ∑ i, ∑ j, M i j * (v j / v i) * (x i)^2 + ∑ i, ∑ j, M i j * (v i / v j) * (x j)^2 := by
    linarith [h_sum3, h_sum4]
  have h_sum6 : ∑ i, ∑ j, M i j * (v i / v j) * (x j)^2 = 
      ∑ i, ∑ j, M i j * (v j / v i) * (x i)^2 := by
    apply sum_matrix_weighted_swap M v x hM_sym
  have h_sum7 : 2 * ∑ i, ∑ j, M i j * x i * x j ≤ 2 * (∑ i, ∑ j, M i j * (v j / v i) * (x i)^2) := by
    linarith [h_sum5, h_sum6]
  have h_sum8 : ∑ i, ∑ j, M i j * (v j / v i) * (x i)^2 = lambda * ∑ i, (x i)^2 := by
    apply double_sum_bound_by_eigenvalue M v x lambda h_eig hv_pos
  linarith [h_sum7, h_sum8]

lemma complex_of_real_conj_eq (r : ℝ) : star (Complex.ofReal r) = Complex.ofReal r := by
  rw [Complex.star_def]
  exact Complex.conj_ofReal r

lemma matrix_real_symm_is_hermitian_aux {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm) :
    (M.map Complex.ofReal).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.map_apply, 
             complex_of_real_conj_eq]
  rw [hM.apply]

lemma step1_euclidean_type_eq :
    EuclideanSpace ℂ (Fin n) = PiLp 2 (fun (_ : Fin n) => ℂ) := by
  rfl

lemma step2_inner_pilp_eq_sum_inner (x y : EuclideanSpace ℂ (Fin n)) :
    ⟪x, y⟫ = ∑ i : Fin n, ⟪x i, y i⟫ := by
  exact PiLp.inner_apply x y

lemma step3_complex_inner_def (a b : ℂ) :
    ⟪a, b⟫ = star a * b := by 
  simp [inner]
  ring

lemma step4_component_inner_eq (x y : EuclideanSpace ℂ (Fin n)) (i : Fin n) :
    ⟪x i, y i⟫ = star (x i) * y i := by
  rw [step3_complex_inner_def (x i) (y i)]

lemma step5_sum_congr (x y : EuclideanSpace ℂ (Fin n)) :
    (∑ i : Fin n, ⟪x i, y i⟫) = ∑ i : Fin n, star (x i) * y i := by
  apply Finset.sum_congr rfl
  intro i _
  exact step4_component_inner_eq x y i

lemma euclidean_inner_eq_sum_conj_mul {n : ℕ} (x y : EuclideanSpace ℂ (Fin n)) :
    ⟪x, y⟫ = ∑ i : Fin n, star (x i) * y i := by
  rw [step2_inner_pilp_eq_sum_inner]
  rw [step5_sum_congr]  

lemma matrix_vec_mul_component {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (x : EuclideanSpace ℂ (Fin n)) (i : Fin n) :
    (Matrix.toEuclideanLin A x) i = ∑ j, A i j * x j := by
  simp [Matrix.mulVec, dotProduct]

lemma inner_matrix_apply_expansion_aux {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (x y : EuclideanSpace ℂ (Fin n)) :
    ⟪Matrix.toEuclideanLin A x, y⟫ = ∑ i, ∑ j, star (A i j) * star (x j) * y i := by
  rw [euclidean_inner_eq_sum_conj_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [matrix_vec_mul_component]
  rw [star_sum]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [StarMul.star_mul]
  ring

lemma double_sum_comm_complex {n : ℕ} (f : Fin n → Fin n → ℂ) :
    ∑ i, ∑ j, f i j = ∑ j, ∑ i, f i j :=
  Finset.sum_comm

lemma complex_inner_expansion {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ)
    (x : EuclideanSpace ℂ (Fin n)) :
  ⟪(Matrix.toEuclideanLin (M.map Complex.ofReal)) x, x⟫ =
    ∑ i, ∑ j, star (x j) * (M i j : ℂ) * x i := by
  classical
  simp [PiLp.inner_apply,
        Matrix.mulVec,
        dotProduct,
        Finset.mul_sum,
        mul_comm,
        mul_left_comm]

lemma abs_complex_inner_le_abs_sum {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (x : EuclideanSpace ℂ (Fin n))
    (hM_nonneg : ∀ i j, 0 ≤ M i j) :
    ‖⟪(Matrix.toEuclideanLin (M.map Complex.ofReal)) x, x⟫‖ ≤
      ∑ i, ∑ j, M i j * ‖x i‖ * ‖x j‖ := by
  classical
  have hinner :
      ⟪(Matrix.toEuclideanLin (M.map Complex.ofReal)) x, x⟫ =
        ∑ i, ∑ j, star (x j) * (M i j : ℂ) * x i :=
    complex_inner_expansion (M := M) (x := x)
  have h₀ :
      ‖⟪(Matrix.toEuclideanLin (M.map Complex.ofReal)) x, x⟫‖ =
        ‖∑ i, ∑ j, star (x j) * (M i j : ℂ) * x i‖ := by
    simp [hinner]
  calc
    ‖⟪(Matrix.toEuclideanLin (M.map Complex.ofReal)) x, x⟫‖
        = ‖∑ i, ∑ j, star (x j) * (M i j : ℂ) * x i‖ := h₀
    _ ≤ ∑ i, ‖∑ j, star (x j) * (M i j : ℂ) * x i‖ := by
          have := norm_sum_le (s := Finset.univ)
            (f := fun i => ∑ j, star (x j) * (M i j : ℂ) * x i)
          simpa using this
    _ ≤ ∑ i, ∑ j, ‖star (x j) * (M i j : ℂ) * x i‖ := by
          refine Finset.sum_le_sum ?_
          intro i hi
          have := norm_sum_le (s := Finset.univ)
            (f := fun j => star (x j) * (M i j : ℂ) * x i)
          simpa using this
    _ = ∑ i, ∑ j, ‖star (x j)‖ * ‖(M i j : ℂ)‖ * ‖x i‖ := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          simp [mul_comm, mul_left_comm]
    _ = ∑ i, ∑ j, (‖x j‖ * M i j * ‖x i‖) := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          have h₁ : ‖(M i j : ℂ)‖ = M i j := by
            rw [Complex.norm_real]
            exact abs_of_nonneg (hM_nonneg i j)
          simp [mul_comm]
          simp [hM_nonneg i j]
    _ = ∑ i, ∑ j, M i j * ‖x i‖ * ‖x j‖ := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          ring

lemma norm_sq_eq_sum_abs_sq {n : ℕ} (x : EuclideanSpace ℂ (Fin n)) :
    ‖x‖^2 = ∑ i, ‖x i‖^2 := by
  rw [PiLp.norm_sq_eq_of_L2]

section AdjointProof

lemma step1_conjTranspose_def (A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    A.conjTranspose i j = star (A j i) := by
  rfl

lemma step2_inner_map_expansion (A : Matrix (Fin n) (Fin n) ℂ) (x y : EuclideanSpace ℂ (Fin n)) :
    ⟪Matrix.toEuclideanLin A x, y⟫ = ∑ i, ∑ j, star (A i j) * star (x j) * y i := by
  exact inner_matrix_apply_expansion_aux A x y

lemma step3_swap_sums (A : Matrix (Fin n) (Fin n) ℂ) (x y : EuclideanSpace ℂ (Fin n)) :
    (∑ i, ∑ j, star (A i j) * star (x j) * y i) = ∑ j, ∑ i, star (A i j) * star (x j) * y i := by
  exact double_sum_comm_complex (fun i j => star (A i j) * star (x j) * y i)

lemma step4_rearrange_terms (A : Matrix (Fin n) (Fin n) ℂ) (x y : EuclideanSpace ℂ (Fin n)) :
    (∑ j, ∑ i, star (A i j) * star (x j) * y i) = ∑ j, star (x j) * (∑ i, star (A i j) * y i) := by
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma step5_inner_sum_is_adjoint_mul (A : Matrix (Fin n) (Fin n) ℂ) (y : EuclideanSpace ℂ (Fin n)) (j : Fin n) :
    (∑ i, star (A i j) * y i) = (Matrix.toEuclideanLin A.conjTranspose y) j := by
  rw [matrix_vec_mul_component]
  apply Finset.sum_congr rfl
  intro i _
  rw [step1_conjTranspose_def]

lemma step6_substitute_adjoint (A : Matrix (Fin n) (Fin n) ℂ) (x y : EuclideanSpace ℂ (Fin n)) :
    (∑ j, star (x j) * (∑ i, star (A i j) * y i)) = 
    ∑ j, star (x j) * (Matrix.toEuclideanLin A.conjTranspose y) j := by
  apply Finset.sum_congr rfl
  intro j _
  rw [step5_inner_sum_is_adjoint_mul]

lemma step7_sum_is_inner_adjoint (A : Matrix (Fin n) (Fin n) ℂ) (x y : EuclideanSpace ℂ (Fin n)) :
    (∑ j, star (x j) * (Matrix.toEuclideanLin A.conjTranspose y) j) = 
    ⟪x, Matrix.toEuclideanLin A.conjTranspose y⟫ := by
  rw [euclidean_inner_eq_sum_conj_mul]

lemma inner_matrix_adjoint_eq_conj_transpose {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (x y : EuclideanSpace ℂ (Fin n)) :
    ⟪Matrix.toEuclideanLin A x, y⟫ = ⟪x, Matrix.toEuclideanLin A.conjTranspose y⟫ := by
  rw [step2_inner_map_expansion]
  rw [step3_swap_sums]
  rw [step4_rearrange_terms]
  rw [step6_substitute_adjoint]
  rw [step7_sum_is_inner_adjoint]

end AdjointProof

section SumManipulationAdjoint

lemma sum_adj_step1_swap (A : Matrix (Fin n) (Fin n) ℂ) (x y : EuclideanSpace ℂ (Fin n)) :
    (∑ i, ∑ j, star (A i j) * star (x j) * y i) = ∑ j, ∑ i, star (A i j) * star (x j) * y i := by
  exact Finset.sum_comm

lemma sum_adj_step2_term_assoc (a b c : ℂ) :
    a * b * c = b * (a * c) := by
  ring

lemma sum_adj_step3_apply_assoc (A : Matrix (Fin n) (Fin n) ℂ) (x y : EuclideanSpace ℂ (Fin n)) :
    (∑ j, ∑ i, star (A i j) * star (x j) * y i) = ∑ j, ∑ i, star (x j) * (star (A i j) * y i) := by
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  exact sum_adj_step2_term_assoc (star (A i j)) (star (x j)) (y i)

lemma sum_adj_step4_factor_out (A : Matrix (Fin n) (Fin n) ℂ) (x y : EuclideanSpace ℂ (Fin n)) :
    (∑ j, ∑ i, star (x j) * (star (A i j) * y i)) = ∑ j, star (x j) * (∑ i, star (A i j) * y i) := by
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]

lemma sum_manipulation_adjoint {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (x y : EuclideanSpace ℂ (Fin n)) :
    (∑ i, ∑ j, star (A i j) * star (x j) * y i) = ∑ j, star (x j) * (∑ i, star (A i j) * y i) := by
  rw [sum_adj_step1_swap]
  rw [sum_adj_step3_apply_assoc]
  rw [sum_adj_step4_factor_out]

end SumManipulationAdjoint

section MatrixInnerAdjoint

lemma mat_adj_step1_vec_component (A : Matrix (Fin n) (Fin n) ℂ) (y : EuclideanSpace ℂ (Fin n)) (j : Fin n) :
    (∑ i, star (A i j) * y i) = (Matrix.toEuclideanLin A.conjTranspose y) j := by
  rw [matrix_vec_mul_component]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.conjTranspose_apply]

lemma mat_adj_step2_subst_vec (A : Matrix (Fin n) (Fin n) ℂ) (x y : EuclideanSpace ℂ (Fin n)) :
    (∑ j, star (x j) * (∑ i, star (A i j) * y i)) = 
    ∑ j, star (x j) * (Matrix.toEuclideanLin A.conjTranspose y) j := by
  apply Finset.sum_congr rfl
  intro j _
  rw [mat_adj_step1_vec_component]

lemma mat_adj_step3_recognize_inner (A : Matrix (Fin n) (Fin n) ℂ) (x y : EuclideanSpace ℂ (Fin n)) :
    (∑ j, star (x j) * (Matrix.toEuclideanLin A.conjTranspose y) j) = 
    ⟪x, Matrix.toEuclideanLin A.conjTranspose y⟫ := by
  rw [euclidean_inner_eq_sum_conj_mul]

lemma matrix_inner_eq_inner_adjoint {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (x y : EuclideanSpace ℂ (Fin n)) :
    ⟪Matrix.toEuclideanLin A x, y⟫ = ⟪x, Matrix.toEuclideanLin A.conjTranspose y⟫ := by
  rw [inner_matrix_apply_expansion_aux]
  rw [sum_manipulation_adjoint]
  rw [mat_adj_step2_subst_vec]
  rw [mat_adj_step3_recognize_inner]

end MatrixInnerAdjoint

section HermitianInnerSymmetry

lemma herm_step1_def {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.IsHermitian) :
    M.conjTranspose = M := by
  exact hM

lemma herm_step2_adjoint_rw (M : Matrix (Fin n) (Fin n) ℂ) (x y : EuclideanSpace ℂ (Fin n)) :
    ⟪Matrix.toEuclideanLin M x, y⟫ = ⟪x, Matrix.toEuclideanLin M.conjTranspose y⟫ := by
  exact matrix_inner_eq_inner_adjoint M x y

lemma herm_step3_subst {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.IsHermitian) (y : EuclideanSpace ℂ (Fin n)) :
    Matrix.toEuclideanLin M.conjTranspose y = Matrix.toEuclideanLin M y := by
  rw [herm_step1_def hM]

lemma hermitian_matrix_induces_symmetric_inner {n : ℕ} 
    (M : Matrix (Fin n) (Fin n) ℂ) 
    (hM : M.IsHermitian) 
    (x y : EuclideanSpace ℂ (Fin n)) :
    ⟪Matrix.toEuclideanLin M x, y⟫ = ⟪x, Matrix.toEuclideanLin M y⟫ := by
  rw [herm_step2_adjoint_rw]
  rw [herm_step3_subst hM]

end HermitianInnerSymmetry

section SelfAdjointDef

variable (T : Euc n →L[ℂ] Euc n)

lemma self_adj_step1_star_def :
    IsSelfAdjoint T ↔ star T = T := by
  exact isSelfAdjoint_iff

lemma self_adj_step2_star_eq_adjoint :
    star T = T.adjoint := by
  rfl

lemma self_adj_step3_adjoint_prop (x y : Euc n) :
    ⟪T.adjoint x, y⟫ = ⟪x, T y⟫ := by
  exact ContinuousLinearMap.adjoint_inner_left T y x

lemma self_adj_step4_vec_ext (u v : Euc n) 
    (h : ∀ y, ⟪u, y⟫ = ⟪v, y⟫) : u = v := by
  refine ext_inner_left ℂ ?_
  intro y
  have h1 : ⟪y, u⟫ = star ⟪u, y⟫ := by simp []
  have h2 : ⟪y, v⟫ = star ⟪v, y⟫ := by simp []
  rw [h1, h2]
  rw [h y]

lemma self_adj_step5_op_ext (A B : Euc n →L[ℂ] Euc n)
    (h : ∀ x y, ⟪A x, y⟫ = ⟪B x, y⟫) : A = B := by
  refine ContinuousLinearMap.ext (fun x => ?_)
  apply self_adj_step4_vec_ext (A x) (B x)
  intro y
  exact h x y

lemma self_adj_step6_compare (h_symm : ∀ x y, ⟪T x, y⟫ = ⟪x, T y⟫) (x y : Euc n) :
    ⟪T x, y⟫ = ⟪T.adjoint x, y⟫ := by
  rw [h_symm]
  rw [self_adj_step3_adjoint_prop]

lemma linear_map_is_self_adjoint_def 
    (h_symm : ∀ x y, ⟪T x, y⟫ = ⟪x, T y⟫) : 
    IsSelfAdjoint T := by
  rw [self_adj_step1_star_def]
  rw [self_adj_step2_star_eq_adjoint]
  apply self_adj_step5_op_ext
  intro x y
  rw [self_adj_step3_adjoint_prop T x y]
  rw [← h_symm x y]

end SelfAdjointDef

section RealSymmToSelfAdjoint

lemma step1_real_symm_map_hermitian (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm) :
    (M.map Complex.ofReal).IsHermitian := by
  exact matrix_real_symm_is_hermitian_aux M hM

lemma step2_inner_product_symmetry (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm) 
    (x y : Euc n) :
    ⟪Matrix.toEuclideanLin (M.map Complex.ofReal) x, y⟫ = 
    ⟪x, Matrix.toEuclideanLin (M.map Complex.ofReal) y⟫ := by
  let M_complex := M.map Complex.ofReal
  have h_herm : M_complex.IsHermitian := step1_real_symm_map_hermitian M hM
  exact hermitian_matrix_induces_symmetric_inner M_complex h_herm x y

lemma step3_clm_symmetry (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm) (x y : Euc n) :
    let T := (Matrix.toEuclideanLin (M.map Complex.ofReal)).toContinuousLinearMap
    ⟪T x, y⟫ = ⟪x, T y⟫ := by
  exact step2_inner_product_symmetry M hM x y

lemma real_symmetric_matrix_to_clm_is_self_adjoint {n : ℕ} 
    (M : Matrix (Fin n) (Fin n) ℝ) (hM_sym : M.IsSymm) :
    IsSelfAdjoint (Matrix.toEuclideanLin (M.map Complex.ofReal)).toContinuousLinearMap := by
  let T := (Matrix.toEuclideanLin (M.map Complex.ofReal)).toContinuousLinearMap
  apply linear_map_is_self_adjoint_def T
  intro x y
  exact step3_clm_symmetry M hM_sym x y

end RealSymmToSelfAdjoint

section NumericalRadiusBound

lemma nr_step1_inner_le_norm_sq (T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) 
    (x : EuclideanSpace ℂ (Fin n)) :
    ‖⟪T x, x⟫‖ ≤ ‖T‖ * ‖x‖^2 := by
  calc
    ‖⟪T x, x⟫‖ ≤ ‖T x‖ * ‖x‖ := norm_inner_le_norm (T x) x
    _ ≤ (‖T‖ * ‖x‖) * ‖x‖ := mul_le_mul_of_nonneg_right (T.le_opNorm x) (norm_nonneg x)
    _ = ‖T‖ * ‖x‖^2 := by ring

lemma nr_step2_unit_inner_le_norm (T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) 
    (x : EuclideanSpace ℂ (Fin n)) (hx : ‖x‖ = 1) :
    ‖⟪T x, x⟫‖ ≤ ‖T‖ := by
  have h := nr_step1_inner_le_norm_sq T x
  rw [hx, one_pow, mul_one] at h
  exact h

lemma nr_step3_range_subset (T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :
    numericalRange T ⊆ Metric.closedBall 0 ‖T‖ := by
  intro z hz
  rcases hz with ⟨x, hx, rfl⟩
  simp only [Metric.mem_closedBall, dist_zero_right]
  exact nr_step2_unit_inner_le_norm T x hx

lemma numericalRadius_le_norm 
    (T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) : 
    numericalRadius T ≤ ‖T‖ := by
  apply Real.sSup_le
  · intro r hr
    rcases hr with ⟨z, hz, rfl⟩
    have h_bound : z ∈ Metric.closedBall 0 ‖T‖ := nr_step3_range_subset T hz
    simp only [Metric.mem_closedBall, dist_zero_right] at h_bound
    exact h_bound
  · exact norm_nonneg T

end NumericalRadiusBound

section SelfAdjointNormBound

lemma sa_step1_polarization 
    (T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (hT : IsSelfAdjoint T) (x y : EuclideanSpace ℂ (Fin n)) :
    4 * (⟪T x, y⟫).re = (⟪T (x + y), x + y⟫).re - (⟪T (x - y), x - y⟫).re := by
  have h_symm : ∀ x y, ⟪T x, y⟫ = ⟪x, T y⟫ := by 
    intro x y
    have h1 : ⟪T x, y⟫ = ⟪x, T.adjoint y⟫ := by
      rw [← ContinuousLinearMap.adjoint_inner_right T x y]
    have h2 : T.adjoint = T := by
      have h_self_adj : star T = T := hT
      have h_star_eq_adjoint : star T = T.adjoint := by rfl
      rw [← h_star_eq_adjoint]
      exact h_self_adj
    rw [h2] at h1
    exact h1
  have h_conj : star ⟪T x, y⟫ = ⟪y, T x⟫ := inner_conj_symm y (T x)
  have h_re : ⟪T x, y⟫ + ⟪T y, x⟫ = 2 * (⟪T x, y⟫).re := by
    have h_eq : ⟪T y, x⟫ = star ⟪T x, y⟫ := by
      rw [h_symm y x]
      rw [h_conj]
    rw [h_eq]
    have h_add_conj : ⟪T x, y⟫ + star ⟪T x, y⟫ = ↑(2 * (⟪T x, y⟫).re) := by
      rw [show star ⟪T x, y⟫ = (starRingEnd ℂ) (⟪T x, y⟫) by rfl]
      exact Complex.add_conj (⟪T x, y⟫)
    rw [h_add_conj]
    simp
  let p_plus := ⟪T (x + y), x + y⟫
  let p_minus := ⟪T (x - y), x - y⟫
  have h_expand : (p_plus - p_minus).re = 2 * (⟪T x, y⟫ + ⟪T y, x⟫).re := by
    have h1 : p_plus = ⟪T (x + y), x + y⟫ := rfl
    have h2 : p_minus = ⟪T (x - y), x - y⟫ := rfl
    rw [h1, h2]
    have h_expand_inner : ⟪T (x + y), x + y⟫ - ⟪T (x - y), x - y⟫ = 2 * (⟪T x, y⟫ + ⟪T y, x⟫) := by
      have h1 : ⟪T (x + y), x + y⟫ = ⟪T x, x⟫ + ⟪T x, y⟫ + ⟪T y, x⟫ + ⟪T y, y⟫ := by
        have h_add : T (x + y) = T x + T y := by simp [map_add]
        rw [h_add]
        simp []
        ring_nf
      have h2 : ⟪T (x - y), x - y⟫ = ⟪T x, x⟫ - ⟪T x, y⟫ - ⟪T y, x⟫ + ⟪T y, y⟫ := by
        have h_sub : T (x - y) = T x - T y := by simp [map_sub]
        rw [h_sub]
        simp []
        ring_nf
      rw [h1, h2]
      ring
    rw [h_expand_inner]
    simp
  have h_simp : (⟪T x, y⟫ + ⟪T y, x⟫).re = 2 * (⟪T x, y⟫).re := by
    rw [h_re]
    simp [Complex.ofReal_re]
  have h_eq1 : ⟪T (x + y), x + y⟫.re - ⟪T (x - y), x - y⟫.re = 
    (p_plus - p_minus).re := by simp [p_plus, p_minus]
  rw [h_eq1]
  rw [h_expand]
  rw [h_simp]
  ring

lemma bound_unit_inner_le_numericalRadius 
    (T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    {u : EuclideanSpace ℂ (Fin n)} (hu : ‖u‖ = 1) :
    ‖⟪T u, u⟫‖ ≤ numericalRadius T := by
  have h_val : ⟪T u, u⟫ ∈ numericalRange T := 
    mem_numericalRange_of_unit hu
  have h_in_set : ‖⟪T u, u⟫‖ ∈ {‖z‖ | z ∈ numericalRange T} := by
    refine ⟨⟪T u, u⟫, h_val, rfl⟩
  unfold numericalRadius
  apply le_csSup
  · refine ⟨‖T‖, ?_⟩
    intro r hr
    rcases hr with ⟨z, hz, rfl⟩
    rcases hz with ⟨x, hx, rfl⟩
    exact nr_step2_unit_inner_le_norm T x hx
  · have h_in_set : ‖⟪T u, u⟫‖ ∈ {r | ∃ z ∈ numericalRange T, r = ‖z‖} := by
      refine ⟨⟪T u, u⟫, h_val, ?_⟩
      rfl
    omega

lemma norm_inner_le_numericalRadius_mul_norm_sq 
    (T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (z : EuclideanSpace ℂ (Fin n)) : 
    ‖⟪T z, z⟫‖ ≤ numericalRadius T * ‖z‖^2 := by
  by_cases hz : z = 0
  · simp [hz]
  · let u := (‖z‖⁻¹ : ℂ) • z
    have hu : ‖u‖ = 1 := by
      rw [norm_smul]
      have h1 : ‖(‖z‖⁻¹ : ℂ)‖ = ‖z‖⁻¹ := by
        have h_real : (‖z‖⁻¹ : ℂ) = (‖z‖⁻¹ : ℝ) := by simp
        rw [h_real]
        simp
      rw [h1]
      field_simp [norm_ne_zero_iff.2 hz]
    have h_inner_exp : ⟪T z, z⟫ = ‖z‖^2 * ⟪T u, u⟫ := by
      have h1 : z = ‖z‖ • u := by
        have h_def : u = (‖z‖⁻¹ : ℂ) • z := rfl
        rw [h_def]
        have h2 : (‖z‖ : ℂ) • ((‖z‖⁻¹ : ℂ) • z) = z := by
          rw [smul_smul]
          have h3 : (‖z‖ : ℂ) * (‖z‖⁻¹ : ℂ) = 1 := by
            field_simp [norm_ne_zero_iff.2 hz]
          rw [h3]
          rw [one_smul]
        exact h2.symm
      rw [h1]
      simp []
      ring_nf
      simp [norm_smul, hu] 
      ring_nf
    have h_le : ‖⟪T u, u⟫‖ ≤ numericalRadius T := 
      bound_unit_inner_le_numericalRadius T hu
    rw [h_inner_exp]
    have h_norm_mul : ‖↑‖z‖ ^ 2 * ⟪T u, u⟫‖ = ↑‖z‖^2 * ‖⟪T u, u⟫‖ := by
      rw [norm_mul]
      simp []
    rw [h_norm_mul]
    have h_nonneg : 0 ≤ ‖z‖ ^ 2 := sq_nonneg ‖z‖
    nlinarith [h_le, h_nonneg]

lemma sa_step2_bound_quad (T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (z : EuclideanSpace ℂ (Fin n)) : 
    |(⟪T z, z⟫).re| ≤ numericalRadius T * ‖z‖^2 := by
  have h_abs_le_norm : |(⟪T z, z⟫).re| ≤ ‖⟪T z, z⟫‖ := 
    Complex.abs_re_le_norm (⟪T z, z⟫)
  have h_norm_le := norm_inner_le_numericalRadius_mul_norm_sq T z
  exact h_abs_le_norm.trans h_norm_le

lemma step3_lemma1_triangle_ineq (a b : ℝ) : 
    a - b ≤ |a| + |b| := by
  have h1 : a ≤ |a| := le_abs_self a
  have h2 : -b ≤ |b| := neg_le_abs b
  have h_add : a + -b ≤ |a| + |b| := add_le_add h1 h2
  rw [sub_eq_add_neg]
  exact h_add

lemma step3_lemma2_bound_plus 
    (T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (x y : EuclideanSpace ℂ (Fin n)) :
    |(⟪T (x + y), x + y⟫).re| ≤ numericalRadius T * ‖x + y‖^2 := by
  exact sa_step2_bound_quad T (x + y)

lemma step3_lemma3_bound_minus 
    (T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (x y : EuclideanSpace ℂ (Fin n)) :
    |(⟪T (x - y), x - y⟫).re| ≤ numericalRadius T * ‖x - y‖^2 := by
  exact sa_step2_bound_quad T (x - y)

lemma step3_lemma4_sum_bounds 
    (T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (x y : EuclideanSpace ℂ (Fin n)) :
    |(⟪T (x + y), x + y⟫).re| + |(⟪T (x - y), x - y⟫).re| ≤ 
    numericalRadius T * (‖x + y‖^2 + ‖x - y‖^2) := by
  have h1 := step3_lemma2_bound_plus T x y
  have h2 := step3_lemma3_bound_minus T x y
  nlinarith

lemma step3_lemma5_parallelogram_law (x y : EuclideanSpace ℂ (Fin n)) :
    ‖x + y‖^2 + ‖x - y‖^2 = 2 * (‖x‖^2 + ‖y‖^2) := by
  have h1 : ‖x + y‖^2 = RCLike.re ⟪x + y, x + y⟫ := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]
  have h2 : ‖x - y‖^2 = RCLike.re ⟪x - y, x - y⟫ := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]
  rw [h1, h2]
  have h_expand : RCLike.re ⟪x + y, x + y⟫ + RCLike.re ⟪x - y, x - y⟫ 
    = 2 * (‖x‖^2 + ‖y‖^2) := by
    have h1 : ⟪x + y, x + y⟫ = ⟪x + y, x⟫ + ⟪x + y, y⟫ := by
      rw [show x + y = x + y by rfl]
      rw [inner_add_right]
    have h2 : ⟪x + y, x⟫ = ⟪x, x⟫ + ⟪y, x⟫ := by
      simp []
    have h3 : ⟪x + y, y⟫ = ⟪x, y⟫ + ⟪y, y⟫ := by
      simp []
    have h4 : RCLike.re ⟪x + y, x + y⟫ = ‖x‖^2 + ‖y‖^2 + 2 * (RCLike.re ⟪x, y⟫) := by
      rw [h1, h2, h3]
      have h4 : RCLike.re (⟪x, x⟫ + ⟪y, x⟫ + (⟪x, y⟫ + ⟪y, y⟫)) 
      = RCLike.re ⟪x, x⟫ + RCLike.re ⟪y, x⟫ + RCLike.re ⟪x, y⟫ + RCLike.re ⟪y, y⟫ := by
        simp [RCLike.re]
        ring
      rw [h4]
      have h5 : RCLike.re ⟪x, x⟫ = ‖x‖^2 := by
        rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]
      have h6 : RCLike.re ⟪y, y⟫ = ‖y‖^2 := by
        rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]
      have h7 : RCLike.re ⟪y, x⟫ = RCLike.re ⟪x, y⟫ := by
        have h_conj : ⟪y, x⟫ = star ⟪x, y⟫ := by
          simp []
        rw [h_conj]
        apply RCLike.conj_re
      rw [h5, h6, h7]
      ring
    have h5 : RCLike.re ⟪x - y, x - y⟫ = ‖x‖^2 + ‖y‖^2 - 2 * (RCLike.re ⟪x, y⟫) := by
      have h8 : ⟪x - y, x - y⟫ = ⟪x, x⟫ - ⟪x, y⟫ - ⟪y, x⟫ + ⟪y, y⟫ := by
        simp only [PiLp.inner_apply, inner_sub_left, inner_sub_right]
        all_goals ring_nf
      rw [h8]
      have h9 : RCLike.re ⟪x, x⟫ = ‖x‖^2 := by
        rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]
      have h10 : RCLike.re ⟪y, y⟫ = ‖y‖^2 := by
        rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]
      have h_conj : ⟪y, x⟫ = star ⟪x, y⟫ := by
        simp []
      have h11 : (⟪x, y⟫ + ⟪y, x⟫).re = 2 * (⟪x, y⟫).re := by
        have h1 : RCLike.re (⟪x, x⟫ - ⟪x, y⟫ - ⟪y, x⟫ + ⟪y, y⟫) = 
          RCLike.re ⟪x, x⟫ + RCLike.re (-⟪x, y⟫) + RCLike.re (-⟪y, x⟫) + RCLike.re ⟪y, y⟫ := by
          simp [Complex.add_re]
          ring
        have h2 : RCLike.re (-⟪x, y⟫) = -RCLike.re ⟪x, y⟫ := by
          simp [Complex.neg_re]
        have h3 : RCLike.re (-⟪y, x⟫) = -RCLike.re ⟪y, x⟫ := by
          simp [Complex.neg_re]
        have h_add_conj : (⟪x, y⟫ + ⟪y, x⟫).re = 2 * (⟪x, y⟫).re := by
          have h_eq : ⟪y, x⟫ = star ⟪x, y⟫ := h_conj
          rw [h_eq]
          have h_add_conj : ⟪x, y⟫ + star ⟪x, y⟫ = ↑(2 * (⟪x, y⟫).re) := by
            rw [show star ⟪x, y⟫ = (starRingEnd ℂ) (⟪x, y⟫) by rfl]
            exact Complex.add_conj (⟪x, y⟫)
          rw [h_add_conj]
          simp
        exact h_add_conj
      have h2_re : RCLike.re (-⟪x, y⟫) = - RCLike.re ⟪x, y⟫ := by
        simp [Complex.neg_re]
      have h3_re : RCLike.re (-⟪y, x⟫) = - RCLike.re ⟪x, y⟫ := by
        have h_eq : -⟪y, x⟫ = -star (⟪x, y⟫) := by
          rw [h_conj]
        rw [h_eq]
        all_goals tauto
      have h5 : RCLike.re (⟪x, x⟫ - ⟪x, y⟫ - ⟪y, x⟫ + ⟪y, y⟫) = 
        RCLike.re ⟪x, x⟫ + RCLike.re ⟪y, y⟫ - 2 * RCLike.re ⟪x, y⟫ := by
        have h_re_distrib : RCLike.re (⟪x, x⟫ - ⟪x, y⟫ - ⟪y, x⟫ + ⟪y, y⟫) = 
          RCLike.re ⟪x, x⟫ - RCLike.re ⟪x, y⟫ - RCLike.re ⟪y, x⟫ + RCLike.re ⟪y, y⟫ := by
          simp [Complex.add_re, Complex.sub_re]
        have h_re_yx : RCLike.re ⟪y, x⟫ = RCLike.re ⟪x, y⟫ := by
          rw [h_conj]
          apply RCLike.conj_re
        rw [h_re_distrib, h_re_yx]
        ring
      rw [h5, h9, h10]
    rw [h4, h5]
    ring
  exact h_expand

lemma step3_lemma6_parallelogram_unit 
    (x y : EuclideanSpace ℂ (Fin n)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ‖x + y‖^2 + ‖x - y‖^2 = 4 := by
  rw [step3_lemma5_parallelogram_law x y]
  rw [hx, hy]
  norm_num

lemma step3_lemma7_bound_by_four_radius 
    (T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (x y : EuclideanSpace ℂ (Fin n)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    |(⟪T (x + y), x + y⟫).re| + |(⟪T (x - y), x - y⟫).re| ≤ 4 * numericalRadius T := by
  have h_bound := step3_lemma4_sum_bounds T x y
  have h_para := step3_lemma6_parallelogram_unit x y hx hy
  rw [h_para] at h_bound
  linarith

lemma step3_lemma8_apply_polarization 
    (T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (hT : IsSelfAdjoint T) (x y : EuclideanSpace ℂ (Fin n)) :
    4 * (⟪T x, y⟫).re = (⟪T (x + y), x + y⟫).re - (⟪T (x - y), x - y⟫).re := by
  exact sa_step1_polarization T hT x y

lemma step3_lemma9_polarization_le_sum_abs 
    (T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (hT : IsSelfAdjoint T) (x y : EuclideanSpace ℂ (Fin n)) :
    4 * (⟪T x, y⟫).re ≤ |(⟪T (x + y), x + y⟫).re| + |(⟪T (x - y), x - y⟫).re| := by
  rw [step3_lemma8_apply_polarization T hT x y]
  exact step3_lemma1_triangle_ineq _ _

lemma step3_lemma10_four_re_le_four_radius 
    (T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (hT : IsSelfAdjoint T) (x y : EuclideanSpace ℂ (Fin n)) 
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    4 * (⟪T x, y⟫).re ≤ 4 * numericalRadius T := by
  have h1 := step3_lemma9_polarization_le_sum_abs T hT x y
  have h2 := step3_lemma7_bound_by_four_radius T x y hx hy
  exact h1.trans h2

lemma sa_step3_polarization_bound 
    (T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (hT : IsSelfAdjoint T) (x y : EuclideanSpace ℂ (Fin n)) 
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    (⟪T x, y⟫).re ≤ numericalRadius T := by
  have h := step3_lemma10_four_re_le_four_radius T hT x y hx hy
  linarith

lemma step4_lemma1_radius_nonneg 
    (T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) : 
    0 ≤ numericalRadius T := by
  apply Real.sSup_nonneg
  intro x hx
  rcases hx with ⟨z, hz, rfl⟩
  apply norm_nonneg

lemma step4_lemma2_normalize_unit (x : EuclideanSpace ℂ (Fin n)) (hx : x ≠ 0) :
    ‖(‖x‖⁻¹ : ℂ) • x‖ = 1 := by
  rw [norm_smul]
  have h1 : ‖(‖x‖⁻¹ : ℂ)‖ = ‖x‖⁻¹ := by
    have h2 : (‖x‖⁻¹ : ℂ) = (↑‖x‖⁻¹ : ℝ) := by simp
    rw [h2]
    simp []
  rw [h1]
  field_simp [norm_ne_zero_iff.mpr hx]

lemma step4_lemma3_normalize_image_unit 
    (T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) 
    (u : EuclideanSpace ℂ (Fin n)) (hTu : T u ≠ 0) :
    ‖(‖T u‖⁻¹ : ℂ) • T u‖ = 1 := by
  exact step4_lemma2_normalize_unit (T u) hTu
  
lemma step4_lemma4_inner_normalized_eq_norm
    (T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) 
    (u : EuclideanSpace ℂ (Fin n)) (hTu : T u ≠ 0) :
    (⟪T u, (‖T u‖⁻¹ : ℂ) • T u⟫).re = ‖T u‖ := by
  let v := (‖T u‖⁻¹ : ℂ) • T u
  rw [inner_smul_right]
  have h_scalar : star (‖T u‖⁻¹ : ℂ) = (‖T u‖⁻¹ : ℂ) := by
    simp [Complex.conj_ofReal]
  have h_inner_self : inner ℂ (T u) (T u) = (↑‖T u‖ : ℂ) ^ 2 := by
    exact inner_self_eq_norm_sq_to_K (T u)
  rw [h_inner_self]
  simp [Complex.ofReal_re]
  field_simp
  ring_nf
  have h_inner_self : inner ℂ (T u) (T u) = (↑‖T u‖ : ℂ) ^ 2 := by
    exact inner_self_eq_norm_sq_to_K (T u)
  rw [← Complex.ofReal_pow, Complex.ofReal_re]

lemma step4_lemma5_norm_image_le_radius 
    (T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) 
    (hT : IsSelfAdjoint T) (u : EuclideanSpace ℂ (Fin n)) (hu : ‖u‖ = 1) :
    ‖T u‖ ≤ numericalRadius T := by
  by_cases hTu : T u = 0
  · rw [hTu, norm_zero]
    exact step4_lemma1_radius_nonneg T
  · let v := (‖T u‖⁻¹ : ℂ) • T u
    have hv : ‖v‖ = 1 := step4_lemma3_normalize_image_unit T u hTu
    have h_bound := sa_step3_polarization_bound T hT u v hu hv
    rw [step4_lemma4_inner_normalized_eq_norm T u hTu] at h_bound
    exact h_bound

lemma norm_le_numericalRadius_of_self_adjoint 
    (T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) 
    (hT : IsSelfAdjoint T) : 
    ‖T‖ ≤ numericalRadius T := by
  apply ContinuousLinearMap.opNorm_le_bound
  · exact step4_lemma1_radius_nonneg T
  · intro x
    by_cases hx : x = 0
    · simp [hx]
    · let u := (‖x‖⁻¹ : ℂ) • x
      have hu : ‖u‖ = 1 := step4_lemma2_normalize_unit x hx
      have h_unit_bound := step4_lemma5_norm_image_le_radius T hT u hu
      dsimp [u] at h_unit_bound
      rw [map_smul, norm_smul] at h_unit_bound
      have hn1 : ‖(↑‖x‖ : ℂ)⁻¹‖ = ‖x‖⁻¹ := by
        simp [Complex.norm_real, norm_inv]
      rw [hn1] at h_unit_bound
      have hx_pos : 0 < ‖x‖ := by
        apply lt_of_le_of_ne (norm_nonneg x) (Ne.symm (norm_ne_zero_iff.mpr hx))
      have : ‖T x‖ ≤ numericalRadius T * ‖x‖ := by
        have h3 : ‖x‖⁻¹ * ‖T x‖ ≤ numericalRadius T := h_unit_bound
        have hx_pos' : 0 < ‖x‖ := hx_pos
        have h4 : ‖T x‖ = ‖x‖ * (‖x‖⁻¹ * ‖T x‖) := by
          field_simp
        rw [h4]
        have h5 : ‖x‖ * (‖x‖⁻¹ * ‖T x‖) ≤ ‖x‖ * numericalRadius T := by
          apply mul_le_mul_of_nonneg_left
          · exact h3
          · exact hx_pos'.le
        have h6 : ‖x‖ * numericalRadius T = numericalRadius T * ‖x‖ := by ring
        linarith [h5, h6]
      exact this

lemma self_adjoint_norm_eq_numericalRadius 
    (T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) 
    (hT : IsSelfAdjoint T) : 
    ‖T‖ = numericalRadius T := by
  apply le_antisymm
  · exact norm_le_numericalRadius_of_self_adjoint T hT
  · exact numericalRadius_le_norm T

lemma step5_lemma1_range_nonempty_of_pos (n : ℕ) (hn : 0 < n) 
    (T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) : 
    (numericalRange T).Nonempty := by
  let e0 := PiLp.basisFun 2 ℂ (Fin n) ⟨0, hn⟩
  have h_norm : ‖e0‖ = 1 := by
    simp [e0]
  use ⟪T e0, e0⟫
  exact mem_numericalRange_of_unit h_norm

lemma step5_lemma2_norm_range_nonempty (n : ℕ) (hn : 0 < n) 
    (T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) : 
    {r | ∃ z ∈ numericalRange T, r = ‖z‖}.Nonempty := by
  rcases step5_lemma1_range_nonempty_of_pos n hn T with ⟨z, hz⟩
  use ‖z‖
  use z

lemma step5_lemma3_zero_dim_norm_zero (h : n = 0) 
    (T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) : 
    ‖T‖ = 0 := by
  haveI : Subsingleton (EuclideanSpace ℂ (Fin n)) := by
    rw [h]
    infer_instance
  have : ∀ x : EuclideanSpace ℂ (Fin n), x = 0 := by
    intro x
    exact Subsingleton.elim x 0
  have hT_zero : T = 0 := by
    ext x
    simp [this x]
  rw [hT_zero]
  exact ContinuousLinearMap.opNorm_zero

lemma s5_1_subsingleton_of_zero (h : n = 0) : 
    Subsingleton (EuclideanSpace ℂ (Fin n)) := by
  rw [h]
  infer_instance

lemma s5_2_op_zero_of_zero_dim (h : n = 0) 
    (T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) : 
    T = 0 := by
  haveI := s5_1_subsingleton_of_zero h
  ext x
  have hx0 : x = 0 := by
    exact Subsingleton.elim x 0
  rw [hx0]
  simp

lemma s5_3_norm_zero_op_eq_zero : ‖(0 : Euc n →L[ℂ] Euc n)‖ = 0 := 
  norm_zero

lemma s5_4_norm_zero_of_zero_dim (h : n = 0) 
    (T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) : 
    ‖T‖ = 0 := by
  rw [s5_2_op_zero_of_zero_dim h T]
  exact s5_3_norm_zero_op_eq_zero

lemma s5_5_radius_le_norm 
    (T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :
    numericalRadius T ≤ ‖T‖ := 
  numericalRadius_le_norm T

lemma s5_6_radius_nonneg 
    (T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :
    0 ≤ numericalRadius T := 
  step4_lemma1_radius_nonneg T

lemma s5_7_radius_zero_of_zero_dim (h : n = 0) 
    (T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :
    numericalRadius T = 0 := by
  have hT_norm_zero : ‖T‖ = 0 := s5_4_norm_zero_of_zero_dim h T
  have h_radius_le_zero : numericalRadius T ≤ 0 := by
    have h_le : numericalRadius T ≤ ‖T‖ := s5_5_radius_le_norm T
    rw [hT_norm_zero] at h_le
    linarith
  have h_radius_ge_zero : 0 ≤ numericalRadius T := s5_6_radius_nonneg T
  linarith

lemma s5_8_pos_of_ne_zero (h : n ≠ 0) : 0 < n := 
  Nat.pos_of_ne_zero h

noncomputable def s5_9_basis_vector (hn : 0 < n) : EuclideanSpace ℂ (Fin n) := 
  PiLp.basisFun 2 ℂ (Fin n) ⟨0, hn⟩

lemma s5_10_basis_norm_one (hn : 0 < n) : 
    ‖s5_9_basis_vector hn‖ = 1 := by
  simp [s5_9_basis_vector, PiLp.basisFun]

lemma s5_11_range_nonempty (hn : 0 < n) 
    (T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) : 
    (numericalRange T).Nonempty := by
  use ⟪T (s5_9_basis_vector hn), s5_9_basis_vector hn⟫
  apply mem_numericalRange_of_unit
  exact s5_10_basis_norm_one hn

lemma s5_12_norm_set_nonempty (hn : 0 < n) 
    (T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) : 
    {r | ∃ z ∈ numericalRange T, r = ‖z‖}.Nonempty := by
  rcases s5_11_range_nonempty hn T with ⟨z, hz⟩
  use ‖z‖, z, hz

lemma s5_13_sup_le_of_nonempty_forall {S : Set ℝ} (h_nonempty : S.Nonempty) 
    (bound : ℝ) (h_forall : ∀ r ∈ S, r ≤ bound) : 
    sSup S ≤ bound := by
  apply csSup_le
  · exact h_nonempty
  · intro r hr
    exact h_forall r hr

lemma s5_14_zero_dim_bound_check (h_n0 : n = 0) (bound : ℝ) (h_bound_nonneg : 0 ≤ bound)
    (T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :
    numericalRadius T ≤ bound := by
  rw [s5_7_radius_zero_of_zero_dim h_n0 T]
  exact h_bound_nonneg

lemma step5_lemma4_spectral_bound_logic (n : ℕ) 
    (T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (bound : ℝ)
    (h_bound_nonneg : 0 ≤ bound)
    (h_forall : ∀ r ∈ {r | ∃ z ∈ numericalRange T, r = ‖z‖}, r ≤ bound) :
    numericalRadius T ≤ bound := by
  by_cases hn : n = 0
  · exact s5_14_zero_dim_bound_check hn bound h_bound_nonneg T
  · have h_pos : 0 < n := s5_8_pos_of_ne_zero hn
    have h_nonempty := s5_12_norm_set_nonempty h_pos T
    exact s5_13_sup_le_of_nonempty_forall h_nonempty bound h_forall

end SelfAdjointNormBound

lemma norm_le_of_positive_eigenvector {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) 
    (v : Fin n → ℝ) (lambda_max : ℝ)
    (hM_sym : M.IsSymm)
    (hM_nonneg : ∀ i j, 0 ≤ M i j)
    (hv_pos : ∀ i, 0 < v i)
    (h_eig : ∀ i, ∑ j, M i j * v j = lambda_max * v i) 
    (hn_nonzero : n ≠ 0) : 
    ‖(Matrix.toEuclideanLin (M.map Complex.ofReal)).toContinuousLinearMap‖ ≤ lambda_max := by
  let T := (Matrix.toEuclideanLin (M.map Complex.ofReal)).toContinuousLinearMap
  have h_sa : IsSelfAdjoint T := by
    exact real_symmetric_matrix_to_clm_is_self_adjoint M hM_sym
  have h_norm_eq : ‖T‖ = numericalRadius T := by
    exact self_adjoint_norm_eq_numericalRadius T h_sa
  have h_lambda_nonneg : 0 ≤ lambda_max := by
    have h_idx : 0 < n := Nat.pos_of_ne_zero hn_nonzero
    let i : Fin n := ⟨0, h_idx⟩
    have h_sum_pos : 0 ≤ ∑ j, M i j * v j := by
      apply Finset.sum_nonneg
      intro j _
      exact mul_nonneg (hM_nonneg i j) (le_of_lt (hv_pos j))
    rw [h_eig i] at h_sum_pos
    have hv_pos_i : 0 < v i := hv_pos i
    exact nonneg_of_mul_nonneg_left h_sum_pos hv_pos_i
  rw [h_norm_eq]
  apply step5_lemma4_spectral_bound_logic n T lambda_max h_lambda_nonneg
  intro r hr
  rcases hr with ⟨z, hz, rfl⟩
  rcases hz with ⟨x, hx, rfl⟩
  have h_bound := abs_complex_inner_le_abs_sum M x hM_nonneg
  have h_quad := real_quad_form_abs_bound M v (fun i => ‖x i‖) lambda_max hM_sym hM_nonneg hv_pos h_eig
  rw [← norm_sq_eq_sum_abs_sq x] at h_quad
  rw [hx, one_pow, mul_one] at h_quad
  exact h_bound.trans h_quad

section HermitianNormBound

noncomputable def hermitianPartReal (n : ℕ) : Matrix (Fin n) (Fin n) ℝ := fun i j => (hermitianPart n i j).re

lemma h01_im_zero (n : ℕ) (i j : Fin n) :
    (hermitianPart n i j).im = 0 := by
  exact hermitianPart_is_real n i j

lemma h02_eq_map_ofReal (n : ℕ) :
    hermitianPart n = (hermitianPartReal n).map Complex.ofReal := by
  ext i j
  simp only [hermitianPartReal, Matrix.map_apply]
  apply Complex.ext
  · rfl
  · simp [h01_im_zero]

lemma h03_real_symm (n : ℕ) : (hermitianPartReal n).IsSymm := by
  rw [Matrix.IsSymm]
  ext i j
  simp only [Matrix.transpose_apply]
  unfold hermitianPartReal hermitianPart
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.conjTranspose_apply, smul_eq_mul]
  rw [Complex.mul_re, Complex.mul_re]
  simp only [div_eq_mul_inv]
  norm_num
  ring

lemma h04_real_nonneg (n : ℕ) (i j : Fin n) :
    0 ≤ hermitianPartReal n i j := by
  exact hermitianPart_nonneg n i j

lemma h05_eig_vec_pos (hn : 2 ≤ n) (i : Fin n) :
    0 < h_eig_vec n i :=
  h_eig_vec_pos hn i

lemma h06_eigen_eq_real (hn : 2 ≤ n) (i : Fin n) :
    ∑ j, hermitianPartReal n i j * h_eig_vec n j = 1 * h_eig_vec n i := by
  simp only [one_mul]
  have h_complex := hermitianPart_mul_eig_vec hn i
  rw [h02_eq_map_ofReal] at h_complex
  simp only [Matrix.map_apply] at h_complex
  rw [← Complex.ofReal_inj]
  exact_mod_cast h_complex

lemma h07_spectral_bound_real (hn : 2 ≤ n) :
    let T := (Matrix.toEuclideanLin ((hermitianPartReal n).map Complex.ofReal)).toContinuousLinearMap
    ‖T‖ ≤ 1 := by
  intro T
  apply norm_le_of_positive_eigenvector (hermitianPartReal n) (h_eig_vec n) 1
  · exact h03_real_symm n
  · exact h04_real_nonneg n
  · exact h05_eig_vec_pos hn
  · exact h06_eigen_eq_real hn
  · omega

lemma hermitianPart_norm_bound_aux (hn : 2 ≤ n) :
    let A := hermitianPart n
    ∀ x : Euc n, ‖(Matrix.toEuclideanLin A) x‖ ≤ 1 * ‖x‖ := by
  intro A x
  rw [one_mul]
  have h_eq : A = (hermitianPartReal n).map Complex.ofReal := h02_eq_map_ofReal n
  rw [h_eq]
  let T := (Matrix.toEuclideanLin ((hermitianPartReal n).map Complex.ofReal)).toContinuousLinearMap
  have h_norm : ‖T‖ ≤ 1 := h07_spectral_bound_real hn
  exact (T.le_opNorm x).trans (mul_le_of_le_one_left (norm_nonneg x) h_norm)

end HermitianNormBound

lemma opNorm_hermitianCLM_le_one (hn : 2 ≤ n) :
    ‖hermitianCLM n‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound
  · exact zero_le_one
  intro x
  convert hermitianPart_norm_bound_aux hn x
  simp only [hermitianCLM, hermitianPart]
  simp [crabbCLM, Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  rfl

lemma opNorm_hermitianCLM_eq_one (hn : 2 ≤ n) :
    ‖hermitianCLM n‖ = 1 := by
  apply le_antisymm
  · exact opNorm_hermitianCLM_le_one hn
  · let v := crabbVecEuc n hn
    have hv_unit : ‖v‖ = 1 := crabbVecEuc_norm_one hn
    have h_inner_one : ⟪crabbCLM n v, v⟫ = 1 := inner_crabbCLM_crabbVecEuc hn
    have h_real_eq : (⟪crabbCLM n v, v⟫).re = (⟪hermitianCLM n v, v⟫).re :=
      inner_eq_real_part v
    have h_herm_inner_one : (⟪hermitianCLM n v, v⟫).re = 1 := by
      rw [← h_real_eq, h_inner_one]
      simp
    have h_le_norm : (⟪hermitianCLM n v, v⟫).re ≤ ‖hermitianCLM n‖ :=
      re_inner_hermitianCLM_le_opNorm n hv_unit
    rw [h_herm_inner_one] at h_le_norm
    exact h_le_norm

end QuickWinLemmas

lemma eigenvalues_bounded_by_one (hn : n ≥ 2) :
    ∀ x : EuclideanSpace ℂ (Fin n), ‖x‖ = 1 → Complex.re ⟪hermitianCLM n x, x⟫ ≤ 1 := by
  intro x hx
  have h_norm := opNorm_hermitianCLM_le_one (n := n) hn
  exact re_inner_le_one_of_opNorm_le (A := hermitianCLM n) (x := x) hx h_norm

lemma hermitian_has_eigenvalue_one (hn : 2 ≤ n) :
    ∃ x : EuclideanSpace ℂ (Fin n), ‖x‖ = 1 ∧ hermitianCLM n x = x := by
  let v := crabbVecEuc n hn
  have hv_unit : ‖v‖ = 1 := crabbVecEuc_norm_one hn
  use v
  constructor
  · exact hv_unit
  · have h_inner_one : ⟪hermitianCLM n v, v⟫ = 1 := by
      have h1 : ⟪crabbCLM n v, v⟫ = 1 := inner_crabbCLM_crabbVecEuc hn
      have h2 := inner_eq_real_part v
      have h3 : (⟪hermitianCLM n v, v⟫).im = 0 := hermitianCLM_im_zero n v
      rw [Complex.ext_iff]
      simp [h3]
      rw [← h2, h1]
      simp
    have h_norm_le : ‖hermitianCLM n v‖ ≤ 1 := by
      calc 
        ‖hermitianCLM n v‖ ≤ ‖hermitianCLM n‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
        _ = ‖hermitianCLM n‖ := by rw [hv_unit, mul_one]
        _ ≤ 1 := opNorm_hermitianCLM_le_one hn
    have h_sub_zero : ‖hermitianCLM n v - v‖^2 = 0 := by
      rw [norm_sub_sq (𝕜 := ℂ)]
      rw [hv_unit]
      simp only [one_pow]
      rw [h_inner_one]
      simp only [RCLike.one_re, mul_one]
      have h_one_le : 1 ≤ ‖hermitianCLM n v‖ := by
        calc
          1 = Complex.re ⟪hermitianCLM n v, v⟫ := by rw [h_inner_one]; simp
          _ ≤ ‖⟪hermitianCLM n v, v⟫‖ := Complex.re_le_norm _
          _ ≤ ‖hermitianCLM n v‖ * ‖v‖ := norm_inner_le_norm _ _
          _ = ‖hermitianCLM n v‖ := by rw [hv_unit, mul_one]
      have h_norm_sq_eq : ‖hermitianCLM n v‖^2 = 1 := by
        nlinarith [h_norm_le, norm_nonneg ((hermitianCLM n) v)]
      nlinarith
    rw [sq_eq_zero_iff] at h_sub_zero
    rw [norm_eq_zero] at h_sub_zero
    exact eq_of_sub_eq_zero h_sub_zero

end SpectralBound

section CrabbInequalities

noncomputable def crabbWeightReal (n : ℕ) (i : Fin (n - 1)) : ℝ :=
  (crabbWeight n i).re

lemma cw01_im_zero (i : Fin (n - 1)) :
    (crabbWeight n i).im = 0 := by
  unfold crabbWeight
  split_ifs <;> simp

lemma cw02_eq_ofReal (i : Fin (n - 1)) :
    crabbWeight n i = crabbWeightReal n i := by
  apply Complex.ext
  · rfl
  · simp [cw01_im_zero]

lemma cw03_nonneg (i : Fin (n - 1)) :
    0 ≤ crabbWeightReal n i := by
  unfold crabbWeightReal crabbWeight
  split_ifs <;> norm_num [Real.sqrt_pos]

lemma cw04_abs_eq (i : Fin (n - 1)) :
    ‖crabbWeight n i‖ = crabbWeightReal n i := by
  rw [cw02_eq_ofReal]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_eq_self]
  exact cw03_nonneg i

lemma cw05_bound_sqrt2_case1 (hn : n > 2) (i : Fin (n - 1)) (h : i.val = 0) :
    crabbWeightReal n i ≤ Real.sqrt 2 := by
  unfold crabbWeightReal crabbWeight
  rw [if_pos h]
  simp
  split_ifs with h_edge
  · exfalso
    rw [h] at h_edge
    omega
  · simp

lemma cw06_bound_sqrt2_case2 (hn : n > 2) (i : Fin (n - 1)) (h : i.val = n - 2) :
    crabbWeightReal n i ≤ Real.sqrt 2 := by
  unfold crabbWeightReal crabbWeight
  by_cases h0 : i.val = 0
  · exfalso
    rw [h] at h0
    omega
  · rw [if_neg h0, if_pos h]
    simp

lemma cw07_bound_sqrt2_case3 (i : Fin (n - 1)) (h1 : i.val ≠ 0) (h2 : i.val ≠ n - 2) :
    crabbWeightReal n i ≤ Real.sqrt 2 := by
  unfold crabbWeightReal crabbWeight
  rw [if_neg h1, if_neg h2]
  simp

lemma cw08_weights_bounded (hn : n > 2) (i : Fin (n - 1)) :
    crabbWeightReal n i ≤ Real.sqrt 2 := by
  by_cases h1 : i.val = 0
  · exact cw05_bound_sqrt2_case1 hn i h1
  · by_cases h2 : i.val = n - 2
    · exact cw06_bound_sqrt2_case2 hn i h2
    · exact cw07_bound_sqrt2_case3 i h1 h2

lemma idx01_cast_lt (i : Fin (n - 1)) : i.val < n := by
  have := i.is_lt
  omega

lemma idx02_succ_lt (i : Fin (n - 1)) : i.val + 1 < n := by
  have := i.is_lt
  omega

def idxCurr (i : Fin (n - 1)) : Fin n := 
  i.castLE (Nat.sub_le n 1)
def idxNext (i : Fin (n - 1)) (hn : n ≥ 1) : Fin n := 
  ⟨i.val + 1, by omega⟩

lemma cs01_term_abs (x : EuclideanSpace ℂ (Fin n)) (i : Fin (n - 1)) :
    ‖crabbWeight n i * x (idxCurr i) * star (x (idxNext i (by have := i.is_lt; omega)))‖ =
    crabbWeightReal n i * ‖x (idxCurr i)‖ * ‖x (idxNext i (by have := i.is_lt; omega))‖ := by
  simp only [norm_mul, norm_star]
  rw [cw04_abs_eq]

lemma cs02_sum_le_sum_abs (x : EuclideanSpace ℂ (Fin n)) :
    ‖∑ i : Fin (n-1), crabbWeight n i * x (idxCurr i) * star (x (idxNext i (by have := i.is_lt; omega)))‖ ≤
    ∑ i : Fin (n-1), crabbWeightReal n i * ‖x (idxCurr i)‖ * ‖x (idxNext i (by have := i.is_lt; omega))‖ := by
  let f := fun i => crabbWeight n i * x (idxCurr i) * star (x (idxNext i (by have := i.is_lt; omega)))
  have h1 := norm_sum_le Finset.univ f
  apply h1.trans
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro i _
  exact cs01_term_abs x i

lemma cs03_real_cauchy_schwarz_sq (f g : Fin (n - 1) → ℝ) :
    (∑ i, f i * g i)^2 ≤ (∑ i, (f i)^2) * (∑ i, (g i)^2) := by
  exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f g

lemma cs04_apply_cs (x : EuclideanSpace ℂ (Fin n)) :
    (∑ i : Fin (n-1), crabbWeightReal n i * ‖x (idxCurr i)‖ * ‖x (idxNext i (by have := i.is_lt; omega))‖)^2 ≤
    (∑ i : Fin (n-1), crabbWeightReal n i * ‖x (idxCurr i)‖^2) *
    (∑ i : Fin (n-1), crabbWeightReal n i * ‖x (idxNext i (by have := i.is_lt; omega))‖^2) := by
  let w_sqrt := fun i => Real.sqrt (crabbWeightReal n i)
  let a := fun i => w_sqrt i * ‖x (idxCurr i)‖
  let b := fun i => w_sqrt i * ‖x (idxNext i (by have := i.is_lt; omega))‖
  have h_split : ∀ i, crabbWeightReal n i = (w_sqrt i)^2 := fun i =>
    (Real.sq_sqrt (cw03_nonneg i)).symm
  have h_term : ∀ i, crabbWeightReal n i * ‖x (idxCurr i)‖ * ‖x (idxNext i (by have := i.is_lt; omega))‖ = a i * b i := by
    intro i
    dsimp [a, b]
    rw [h_split i]
    ring
  rw [Finset.sum_congr rfl (fun i _ => h_term i)]
  have h_CS := cs03_real_cauchy_schwarz_sq a b
  have h_rhs_a : ∀ i, (a i)^2 = crabbWeightReal n i * ‖x (idxCurr i)‖^2 := by
    intro i; dsimp [a]; rw [mul_pow, Real.sq_sqrt (cw03_nonneg i)]
  have h_rhs_b : ∀ i, (b i)^2 = crabbWeightReal n i * ‖x (idxNext i (by have := i.is_lt; omega))‖^2 := by
    intro i; dsimp [b]; rw [mul_pow, Real.sq_sqrt (cw03_nonneg i)]
  simp_rw [h_rhs_a, h_rhs_b] at h_CS
  exact h_CS


lemma weighted_cauchy_schwarz_aux (x : EuclideanSpace ℂ (Fin n)) :
    ‖∑ i : Fin (n-1), crabbWeight n i * x (idxCurr i) * star (x (idxNext i (by have := i.is_lt; omega)))‖^2 ≤
    (∑ i : Fin (n-1), crabbWeightReal n i * ‖x (idxCurr i)‖^2) *
    (∑ i : Fin (n-1), crabbWeightReal n i * ‖x (idxNext i (by have := i.is_lt; omega))‖^2) := by
  have h1 := cs02_sum_le_sum_abs x
  have h1_sq : ‖∑ i : Fin (n-1), crabbWeight n i * x (idxCurr i) *  
    star (x (idxNext i (by have := i.is_lt; omega)))‖^2 ≤
    (∑ i : Fin (n-1), crabbWeightReal n i * ‖x (idxCurr i)‖ * 
    ‖x (idxNext i (by have := i.is_lt; omega))‖)^2 := by
    nlinarith [h1, norm_nonneg (∑ i : Fin (n-1), crabbWeight n i * x (idxCurr i) * star (x (idxNext i (by have := i.is_lt; omega))))]
  have h2 := cs04_apply_cs x
  exact h1_sq.trans h2

lemma sum01_bound_by_max (hn : n > 2) (f : Fin (n-1) → ℝ) (h_nonneg : ∀ i, 0 ≤ f i) :
    ∑ i, crabbWeightReal n i * f i ≤ Real.sqrt 2 * ∑ i, f i := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_right
  · exact cw08_weights_bounded hn i
  · exact h_nonneg i

lemma sum02_norm_sq_eq (x : EuclideanSpace ℂ (Fin n)) (i : Fin n) : 
  ‖x i‖^2 = ‖x i‖^2 := by
  rfl

lemma sum03_total_norm (x : EuclideanSpace ℂ (Fin n)) :
    ∑ i : Fin n, ‖x i‖^2 = ‖x‖^2 := by
  rw [PiLp.norm_sq_eq_of_L2]

lemma product_bound_am_gm (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hsum : a + b ≤ 2) :
    a * b ≤ 1 := by
  nlinarith [sq_nonneg (a - b)]

end CrabbInequalities

section RotationDefinitions

variable {n : ℕ}

noncomputable def rotationMatrix (n : ℕ) (z : ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal (fun i => z ^ (i : ℕ))

lemma rotationMatrix_apply (n : ℕ) (z : ℂ) (i j : Fin n) :
    rotationMatrix n z i j = if i = j then z ^ (i : ℕ) else 0 := by
  simp [rotationMatrix, Matrix.diagonal_apply]

lemma rotationMatrix_mulVec (n : ℕ) (z : ℂ) (v : Euc n) (i : Fin n) :
    (Matrix.mulVec (rotationMatrix n z) v) i = z ^ (i : ℕ) * v i := by
  rw [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single i]
  · rw [rotationMatrix_apply, if_pos rfl]
  · intro j _ hij
    rw [rotationMatrix_apply, if_neg hij.symm, zero_mul]
  · simp

lemma rotationMatrix_star (n : ℕ) (z : ℂ) :
    (rotationMatrix n z).conjTranspose = rotationMatrix n (star z) := by
  ext i j
  simp only [rotationMatrix, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h]
    intro h'
    have : i = j := by
      rw [← h']
    contradiction

end RotationDefinitions

section RotationUnitary

variable {n : ℕ}

lemma rotation_preserves_norm (n : ℕ) {z : ℂ} (hz : ‖z‖ = 1) (v : Euc n) :
    ‖Matrix.toEuclideanLin (rotationMatrix n z) v‖ = ‖v‖ := by
  rw [matrix_toEuclideanLin_apply_toLp]
  simp only [PiLp.norm_eq_of_L2, Real.sqrt_inj (Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  apply Finset.sum_congr rfl
  intro i _
  rw [rotationMatrix_mulVec]
  simp only [norm_mul, norm_pow, hz, one_pow, one_mul]

section RotationUnitaryConstruction

lemma rot_z_mul_conj {z : ℂ} (hz : ‖z‖ = 1) : z * star z = 1 := by
  have h : z * star z = ↑‖z‖^2 := by
    have h1 : z * star z = (Complex.normSq z) := by
      simp [Complex.normSq, Complex.mul_conj]
    have h2 : (Complex.normSq z) = ‖z‖^2 := by
      simp [Complex.normSq_eq_norm_sq]
    rw [h1, h2]
    norm_num
  rw [h, hz]
  norm_num

lemma rot_conj_mul_z {z : ℂ} (hz : ‖z‖ = 1) : star z * z = 1 := by
  rw [mul_comm, rot_z_mul_conj hz]

lemma rot_pow_mul_conj_pow (k : ℕ) {z : ℂ} (hz : ‖z‖ = 1) :
    z ^ k * (star z) ^ k = 1 := by
  rw [← mul_pow, rot_z_mul_conj hz, one_pow]

lemma rot_conj_pow_mul_pow (k : ℕ) {z : ℂ} (hz : ‖z‖ = 1) :
    (star z) ^ k * z ^ k = 1 := by
  rw [← mul_pow, rot_conj_mul_z hz, one_pow]

lemma rot_mat_mul_entry (z w : ℂ) (i j : Fin n) :
    (rotationMatrix n z * rotationMatrix n w) i j = (rotationMatrix n (z * w)) i j := by
  rw [Matrix.mul_apply]
  simp only [rotationMatrix_apply]
  by_cases h : i = j
  · subst h
    rw [Finset.sum_eq_single i]
    · simp [mul_pow]
    · intro k _ hk; simp [hk.symm]
    · simp
  · rw [Finset.sum_eq_zero]
    · simp [h]
    · intro x hx
      simp []
      omega

lemma rot_mat_mul_distrib (z w : ℂ) :
    rotationMatrix n z * rotationMatrix n w = rotationMatrix n (z * w) := by
  ext i j
  exact rot_mat_mul_entry z w i j

lemma rot_mat_one_is_one :
    rotationMatrix n 1 = (1 : Matrix (Fin n) (Fin n) ℂ) := by
  ext i j
  simp [rotationMatrix_apply, Matrix.one_apply, one_pow]

lemma rot_mat_mul_conj_eq_one {z : ℂ} (hz : ‖z‖ = 1) :
    rotationMatrix n z * rotationMatrix n (star z) = 1 := by
  rw [rot_mat_mul_distrib, rot_z_mul_conj hz, rot_mat_one_is_one]

lemma rot_mat_conj_mul_eq_one {z : ℂ} (hz : ‖z‖ = 1) :
    rotationMatrix n (star z) * rotationMatrix n z = 1 := by
  rw [rot_mat_mul_distrib, rot_conj_mul_z hz, rot_mat_one_is_one]

lemma rot_lin_comp (z w : ℂ) :
    (Matrix.toEuclideanLin (rotationMatrix n z)).comp (Matrix.toEuclideanLin (rotationMatrix n w)) =
    Matrix.toEuclideanLin (rotationMatrix n (z * w)) := by
  ext v
  simp [rotationMatrix_mulVec, rot_mat_mul_distrib]
  
lemma rot_lin_one_id :
    Matrix.toEuclideanLin (1 : Matrix (Fin n) (Fin n) ℂ) = ContinuousLinearMap.id ℂ (Euc n) := by
  ext v i
  simp []

lemma rot_comp_conj_eq_id {z : ℂ} (hz : ‖z‖ = 1) :
    (Matrix.toEuclideanLin (rotationMatrix n z)).comp (Matrix.toEuclideanLin (rotationMatrix n (star z))) =
    ContinuousLinearMap.id ℂ (Euc n) := by
  rw [rot_lin_comp, rot_z_mul_conj hz, rot_mat_one_is_one, rot_lin_one_id]

lemma rot_conj_comp_eq_id {z : ℂ} (hz : ‖z‖ = 1) :
    (Matrix.toEuclideanLin (rotationMatrix n (star z))).comp (Matrix.toEuclideanLin (rotationMatrix n z)) =
    ContinuousLinearMap.id ℂ (Euc n) := by
  rw [rot_lin_comp, rot_conj_mul_z hz, rot_mat_one_is_one, rot_lin_one_id]

lemma rot_left_inv_apply {z : ℂ} (hz : ‖z‖ = 1) (v : Euc n) :
    Matrix.toEuclideanLin (rotationMatrix n (star z)) (Matrix.toEuclideanLin (rotationMatrix n z) v) = v := by
  let f := Matrix.toEuclideanLin (rotationMatrix n (star z))
  let g := Matrix.toEuclideanLin (rotationMatrix n z)
  show (f.comp g) v = v
  rw [rot_conj_comp_eq_id hz]
  rfl

lemma rot_right_inv_apply {z : ℂ} (hz : ‖z‖ = 1) (v : Euc n) :
    Matrix.toEuclideanLin (rotationMatrix n z) (Matrix.toEuclideanLin (rotationMatrix n (star z)) v) = v := by
  let f := Matrix.toEuclideanLin (rotationMatrix n z)
  let g := Matrix.toEuclideanLin (rotationMatrix n (star z))
  show (f.comp g) v = v
  rw [rot_comp_conj_eq_id hz]
  rfl

noncomputable def rotationLinearEquiv (n : ℕ) {z : ℂ} (hz : ‖z‖ = 1) : Euc n ≃ₗ[ℂ] Euc n :=
  { toFun    := Matrix.toEuclideanLin (rotationMatrix n z)
    invFun   := Matrix.toEuclideanLin (rotationMatrix n (star z))
    map_add' := map_add _
    map_smul' := map_smul _
    left_inv := rot_left_inv_apply hz
    right_inv := rot_right_inv_apply hz }

lemma rot_z_pow_norm {z : ℂ} (hz : ‖z‖ = 1) (i : Fin n) :
    ‖z ^ (i : ℕ)‖ = 1 := by
  simp [norm_pow, hz]

lemma rot_vec_apply_norm_sq (n : ℕ) {z : ℂ} (hz : ‖z‖ = 1) (v : Euc n) (i : Fin n) :
    ‖(Matrix.toEuclideanLin (rotationMatrix n z) v) i‖^2 = ‖v i‖^2 := by
  simp [rotationMatrix_mulVec, hz]

lemma rot_preserves_norm_sq (n : ℕ) {z : ℂ} (hz : ‖z‖ = 1) (v : Euc n) :
    ‖Matrix.toEuclideanLin (rotationMatrix n z) v‖^2 = ‖v‖^2 := by
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro i _
  exact rot_vec_apply_norm_sq n hz v i

lemma rot_preserves_norm_final (n : ℕ) {z : ℂ} (hz : ‖z‖ = 1) (v : Euc n) :
    ‖Matrix.toEuclideanLin (rotationMatrix n z) v‖ = ‖v‖ := by
  have h : ‖Matrix.toEuclideanLin (rotationMatrix n z) v‖^2 = ‖v‖^2 := rot_preserves_norm_sq n hz v
  have h_nonneg : ‖Matrix.toEuclideanLin (rotationMatrix n z) v‖ ≥ 0 := norm_nonneg _
  have h_nonneg' : ‖v‖ ≥ 0 := norm_nonneg _
  nlinarith [h, h_nonneg, h_nonneg']

end RotationUnitaryConstruction

noncomputable def rotationUnitary (n : ℕ) {z : ℂ} (hz : ‖z‖ = 1) : Euc n ≃ₗᵢ[ℂ] Euc n :=
  LinearIsometryEquiv.mk
    (rotationLinearEquiv n hz)
    (rot_preserves_norm_final n hz)

end RotationUnitary

section CrabbSymmetry

lemma diag_conj_mul_dense_mul_diag_entry (A : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℂ) (i j : Fin n) :
    (Matrix.diagonal (star ∘ d) * A * Matrix.diagonal d) i j = star (d i) * A i j * d j := by
  simp only [Matrix.mul_apply, Matrix.diagonal_apply]
  have h1 : ∀ (l : Fin n), ∑ (k : Fin n), (if i = k then star (d i) else 0) * A k l = star (d i) * A i l := by
    intro l
    rw [Finset.sum_eq_single i]
    · simp
    · intro k _ hki; simp []; omega
    · simp
  simp []
  
lemma star_z_pow_mul_z_pow_succ {z : ℂ} (hz : ‖z‖ = 1) (i : ℕ) :
    star z ^ i * z ^ (i + 1) = z := by
  have h_comm : star z ^ i * z ^ (i + 1) = (star z * z) ^ i * z := by
    rw [pow_succ]
    ring
  have h_one : star z * z = 1 := by
    have h_comm : star z * z = z * star z := by
      ring
    rw [h_comm, rot_z_mul_conj hz]
  rw [h_comm, h_one, one_pow, one_mul]

lemma crabb_matrix_rotation_conjugation_entry (n : ℕ) {z : ℂ} (hz : ‖z‖ = 1) (i j : Fin n) :
    (rotationMatrix n (star z) * CrabbMatrix n * rotationMatrix n z) i j =
    (z • CrabbMatrix n) i j := by
  rw [Matrix.smul_apply]
  simp [Matrix.mul_apply, rotationMatrix, Matrix.diagonal_apply]
  by_cases h_nz : CrabbMatrix n i j = 0
  · simp [h_nz]
  · have h_super : j.val = i.val + 1 := by
      have h := crabbMatrix_superdiag i j h_nz
      simpa using h
    rw [h_super]
    have h_simpl : ((starRingEnd ℂ) z ^ i.val) * (CrabbMatrix n i j) * (z ^ (i.val + 1)) =
        ((starRingEnd ℂ) z ^ i.val * z ^ (i.val + 1)) * CrabbMatrix n i j := by ring
    rw [h_simpl]
    have h_pow : (starRingEnd ℂ) z ^ i.val * z ^ (i.val + 1) = z := by
      rw [show (starRingEnd ℂ) z = star z by rfl]
      exact star_z_pow_mul_z_pow_succ hz i.val
    rw [h_pow]

lemma crabb_matrix_rotation_conjugation_eq (n : ℕ) {z : ℂ} (hz : ‖z‖ = 1) :
    rotationMatrix n (star z) * CrabbMatrix n * rotationMatrix n z = z • CrabbMatrix n := by
  ext i j
  exact crabb_matrix_rotation_conjugation_entry n hz i j

lemma unitary_conjugate_eq_matrix_conjugate
    (U : Euc n ≃ₗᵢ[ℂ] Euc n) (A M M_inv : Matrix (Fin n) (Fin n) ℂ)
    (hU : U.toLinearEquiv.toFun = Matrix.toEuclideanLin M)
    (hU_inv : U.toLinearEquiv.invFun = Matrix.toEuclideanLin M_inv) :
    unitary_conjugate U (Matrix.toEuclideanLin A).toContinuousLinearMap =
    (Matrix.toEuclideanLin (M_inv * A * M)).toContinuousLinearMap := by
  ext v i
  simp [unitary_conjugate, ContinuousLinearMap.comp_apply]
  all_goals
    try rw [←hU, ←hU_inv]
    try simp [matrix_toEuclideanLin_apply]
    try aesop

lemma crabb_unitary_conjugate (n : ℕ) {z : ℂ} (hz : ‖z‖ = 1) :
    unitary_conjugate (rotationUnitary n hz) (crabbCLM n) = z • crabbCLM n := by
  let U := rotationUnitary n hz
  let M := rotationMatrix n z
  let M_inv := rotationMatrix n (star z)
  have h_conj := unitary_conjugate_eq_matrix_conjugate U (CrabbMatrix n) M M_inv rfl rfl
  rw [h_conj]
  rw [crabb_matrix_rotation_conjugation_eq n hz]
  simp [crabbCLM]

lemma numericalRange_smul (α : ℂ) (A : E →L[ℂ] E) :
    numericalRange (α • A) = (star α • ·) '' numericalRange A := by
  ext w
  constructor
  · rintro ⟨x, hx, rfl⟩
    use ⟪A x, x⟫
    constructor
    · apply mem_numericalRange_of_unit (A := A) hx
    · simp only [ContinuousLinearMap.smul_apply, inner_smul_left]
      rfl
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    use x
    constructor
    · exact hx
    · simp only [ContinuousLinearMap.smul_apply, inner_smul_left]
      rfl

lemma nr_unitary_step1_subset (U : E ≃ₗᵢ[ℂ] E) (A : E →L[ℂ] E) :
    numericalRange (unitary_conjugate U A) ⊆ numericalRange A := by
  intro z hz
  rcases hz with ⟨x, hx, rfl⟩
  use U x
  constructor
  · simp [hx]
  · rw [unitary_conjugate_inner]

lemma nr_unitary_step2_subset_symm (U : E ≃ₗᵢ[ℂ] E) (A : E →L[ℂ] E) :
    numericalRange A ⊆ numericalRange (unitary_conjugate U A) := by
  intro z hz
  rcases hz with ⟨x, hx, rfl⟩
  use U.symm x
  constructor
  · simp [hx]
  · rw [unitary_conjugate_inner]
    simp

lemma numericalRange_unitary_invariant (U : E ≃ₗᵢ[ℂ] E) (A : E →L[ℂ] E) :
    numericalRange (unitary_conjugate U A) = numericalRange A :=
  Subset.antisymm (nr_unitary_step1_subset U A) (nr_unitary_step2_subset_symm U A)

lemma nr_crabb_rotation_invariant (n : ℕ) {z : ℂ} (hz : ‖z‖ = 1) :
    numericalRange (z • crabbCLM n) = numericalRange (crabbCLM n) := by
  have h_conj : z • crabbCLM n = unitary_conjugate (rotationUnitary n hz) (crabbCLM n) := by
    rw [crabb_unitary_conjugate n hz]
  rw [h_conj]
  rw [numericalRange_unitary_invariant]

lemma set_smul_inv_cancel {S : Set ℂ} {z : ℂ} (hz : ‖z‖ = 1) :
    (z • ·) '' ((star z • ·) '' S) = S := by
  rw [Set.image_image]
  have h1 : ∀ x : ℂ, z • (star z • x) = x := by
    intro x
    calc
      z • (star z • x) = (z * star z) • x := by simp []; ring
      _ = 1 • x := by 
        have h2 : z * star z = 1 := rot_z_mul_conj hz
        rw [h2]
        simp
      _ = x := by simp
  have h2 : (fun a => z * ((starRingEnd ℂ) z * a)) = (id : ℂ → ℂ) := by
    funext a
    calc
      z * ((starRingEnd ℂ) z * a) = z • (star z • a) := by simp [smul_eq_mul]
      _ = a := h1 a
  simp [h2, Set.image_id]

lemma nr_scaling_prop {z : ℂ} (_hz : ‖z‖ = 1) (A : E →L[ℂ] E) :
    numericalRange (z • A) = (star z • ·) '' numericalRange A := by
  rw [numericalRange_smul]

lemma circular_logic_core (S : Set ℂ) (z : ℂ) (hz : ‖z‖ = 1)
    (h_invariant : (star z • ·) '' S = S) :
    (z • ·) '' S = S := by
  have h : (z • ·) '' ((star z • ·) '' S) = S := set_smul_inv_cancel hz
  rw [h_invariant] at h
  exact h

lemma crabb_numericalRange_circular (_hn : n ≥ 1) :
    ∀ z : ℂ, ‖z‖ = 1 → (z • ·) '' numericalRange (crabbCLM n) = numericalRange (crabbCLM n) := by
  intro z hz
  have h1 : numericalRange (z • crabbCLM n) = numericalRange (crabbCLM n) :=
    nr_crabb_rotation_invariant n hz
  have h2 : numericalRange (z • crabbCLM n) = (star z • ·) '' numericalRange (crabbCLM n) :=
    nr_scaling_prop hz (crabbCLM n)
  have h_inv : (star z • ·) '' numericalRange (crabbCLM n) = numericalRange (crabbCLM n) := by
    rw [← h2, h1]
  exact circular_logic_core (numericalRange (crabbCLM n)) z hz h_inv

end CrabbSymmetry

section NumericalRadiusCalculation

variable {A : E →L[ℂ] E}

lemma range_re_nonempty (h : (numericalRange (A : E →L[ℂ] E)).Nonempty) :
    (Complex.re '' numericalRange A).Nonempty := by
  rcases h with ⟨z, hz⟩
  use z.re
  use z

lemma re_le_norm_in_range (z : ℂ) (_hz : z ∈ (numericalRange (A : E →L[ℂ] E))) :
    z.re ≤ ‖z‖ := by
  exact Complex.re_le_norm z

def nrNorms (A : E →L[ℂ] E) : Set ℝ :=
  {r | ∃ z ∈ numericalRange A, r = ‖z‖}

def nrRe (A : E →L[ℂ] E) : Set ℝ :=
  Complex.re '' numericalRange A

lemma nr_norm_set_eq_image :
    nrNorms A = (norm) '' numericalRange A := by
  ext r
  simp [nrNorms, Set.mem_image]
  aesop
   
lemma nr_re_set_eq_image :
    nrRe A = Complex.re '' numericalRange A := rfl

lemma nr_norms_subset_interval :
    nrNorms A ⊆ Set.Iic ‖A‖ := by
  intro r hr
  rcases hr with ⟨z, hz, rfl⟩
  exact norm_le_opNorm_of_mem_numericalRange hz

lemma nr_norms_bdd_above :
    BddAbove (nrNorms A) := by
  use ‖A‖
  intro r hr
  exact nr_norms_subset_interval hr

lemma radius_eq_sup_norms :
    numericalRadius A = sSup (nrNorms A) := rfl

lemma norm_le_radius_of_mem_set (_h_nonempty : (numericalRange A).Nonempty) (r : ℝ) (hr : r ∈ nrNorms A) :
    r ≤ numericalRadius A := by
  rw [radius_eq_sup_norms]
  apply le_csSup
  · exact nr_norms_bdd_above
  · exact hr

lemma norm_z_le_radius (h_nonempty : (numericalRange A).Nonempty) (z : ℂ) (hz : z ∈ numericalRange A) :
    ‖z‖ ≤ numericalRadius A := by
  apply norm_le_radius_of_mem_set h_nonempty
  use z, hz

lemma re_le_norm_z (z : ℂ) : z.re ≤ ‖z‖ := by
  exact Complex.re_le_norm z

lemma re_le_norm_of_mem (z : ℂ) (_hz : z ∈ numericalRange A) :
    z.re ≤ ‖z‖ :=
  re_le_norm_z z

lemma re_le_radius_of_mem (h_nonempty : (numericalRange A).Nonempty) (z : ℂ) (hz : z ∈ numericalRange A) :
    z.re ≤ numericalRadius A := by
  have h1 := re_le_norm_z z
  have h2 := norm_z_le_radius h_nonempty z hz
  exact h1.trans h2

lemma nr_re_bounded_by_radius (h_nonempty : (numericalRange A).Nonempty) (r : ℝ) (hr : r ∈ nrRe A) :
    r ≤ numericalRadius A := by
  rcases hr with ⟨z, hz, rfl⟩
  exact re_le_radius_of_mem h_nonempty z hz

lemma nr_re_bdd_above_by_radius (h_nonempty : (numericalRange A).Nonempty) :
    BddAbove (nrRe A) := by
  use numericalRadius A
  intro r hr
  exact nr_re_bounded_by_radius h_nonempty r hr

lemma sup_le_of_forall_le_bound {S : Set ℝ} (h_nonempty : S.Nonempty) (B : ℝ) (h : ∀ x ∈ S, x ≤ B) :
    sSup S ≤ B := by
  apply csSup_le h_nonempty h

lemma sup_re_le_numericalRadius (h_nonempty : (numericalRange A).Nonempty) :
    sSup (Complex.re '' numericalRange A) ≤ numericalRadius A := by
  have h_set : Complex.re '' numericalRange A = nrRe A := rfl
  rw [h_set]
  have h_re_nonempty : (nrRe A).Nonempty := by
    rcases h_nonempty with ⟨z, hz⟩
    use z.re, z, hz
  apply sup_le_of_forall_le_bound h_re_nonempty
  intro r hr
  exact nr_re_bounded_by_radius h_nonempty r hr

lemma exists_rotate_to_real (z : ℂ) (hz_ne : z ≠ 0) :
    ∃ w : ℂ, ‖w‖ = 1 ∧ (w * z).im = 0 ∧ (w * z).re = ‖z‖ := by
  let w := (‖z‖ : ℂ) / z
  use w
  constructor
  · have h_norm : ‖w‖ = ‖(‖z‖ : ℂ)‖ / ‖z‖ := by simp [w]
    rw [h_norm]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg z)]
    have hz_norm_ne : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz_ne
    rw [div_self hz_norm_ne]
  · constructor
    · field_simp [w]
      rw [div_mul_cancel₀ _ hz_ne]
      simp
    · field_simp [w]
      rw [div_mul_cancel₀ _ hz_ne]
      simp

lemma mem_of_circular_rotation (z : ℂ) (hz : z ∈ numericalRange A)
    (h_circ : ∀ w : ℂ, ‖w‖ = 1 → (w • ·) '' numericalRange A = numericalRange A)
    (w : ℂ) (hw : ‖w‖ = 1) :
    w * z ∈ numericalRange A := by
  have h_set_eq : (w • ·) '' numericalRange A = numericalRange A := h_circ w hw
  have h_mem_image : w • z ∈ (w • ·) '' numericalRange A := Set.mem_image_of_mem _ hz
  rw [h_set_eq] at h_mem_image
  simp [smul_eq_mul] at h_mem_image
  exact h_mem_image

lemma norm_eq_rotated_re (z : ℂ) (hz : z ∈ numericalRange A)
    (h_circ : ∀ w : ℂ, ‖w‖ = 1 → (w • ·) '' numericalRange A = numericalRange A) :
    ∃ z' ∈ numericalRange A, z'.re = ‖z‖ := by
  by_cases h0 : z = 0
  · subst h0
    use 0, hz
    simp
  · rcases exists_rotate_to_real z h0 with ⟨w, hw_norm, _, hw_re⟩
    use w * z
    constructor
    · exact mem_of_circular_rotation z hz h_circ w hw_norm
    · exact hw_re


lemma norm_le_sup_re (z : ℂ) (hz : z ∈ numericalRange A)
    (h_circ : ∀ w : ℂ, ‖w‖ = 1 → (w • ·) '' numericalRange A = numericalRange A)
    (h_bdd : BddAbove (Complex.re '' numericalRange A)) :
    ‖z‖ ≤ sSup (Complex.re '' numericalRange A) := by
  rcases norm_eq_rotated_re z hz h_circ with ⟨z', hz', h_eq⟩
  rw [← h_eq]
  apply le_csSup h_bdd
  simp []
  aesop

lemma numerical_range_re_bdd_above :
    BddAbove (Complex.re '' numericalRange A) := by
  use ‖A‖
  rintro r ⟨z, hz, rfl⟩
  calc
    z.re ≤ ‖z‖ := re_le_norm_in_range z hz
    _ ≤ ‖A‖ := norm_le_opNorm_of_mem_numericalRange hz
  
lemma nr_re_set_bdd_above :
    BddAbove (nrRe A) := by
  use ‖A‖
  rintro r ⟨z, hz, rfl⟩
  calc
    z.re ≤ ‖z‖ := Complex.re_le_norm z
    _ ≤ ‖A‖ := norm_le_opNorm_of_mem_numericalRange hz

lemma nr_z_norm_le_sup_re_aux (z : ℂ) (hz : z ∈ numericalRange A)
    (h_circ : ∀ w : ℂ, ‖w‖ = 1 → (w • ·) '' numericalRange A = numericalRange A) :
    ‖z‖ ≤ sSup (nrRe A) := by
  rw [nr_re_set_eq_image]
  apply norm_le_sup_re z hz h_circ
  rw [← nr_re_set_eq_image]
  exact nr_re_set_bdd_above

lemma nr_norm_elt_le_sup_re (r : ℝ) (hr : r ∈ nrNorms A)
    (h_circ : ∀ w : ℂ, ‖w‖ = 1 → (w • ·) '' numericalRange A = numericalRange A) :
    r ≤ sSup (nrRe A) := by
  rcases hr with ⟨z, hz, rfl⟩
  exact nr_z_norm_le_sup_re_aux z hz h_circ

lemma nr_norm_set_nonempty (h_nonempty : (numericalRange A).Nonempty) :
    (nrNorms A).Nonempty := by
  rcases h_nonempty with ⟨z, hz⟩
  use ‖z‖, z, hz

lemma nr_re_set_nonempty (h_nonempty : (numericalRange A).Nonempty) :
    (nrRe A).Nonempty := by
  rcases h_nonempty with ⟨z, hz⟩
  use z.re, z, hz

lemma nr_sup_le_of_forall_le (S : Set ℝ) (B : ℝ)
    (hS_nonempty : S.Nonempty) (h_le : ∀ x ∈ S, x ≤ B) :
    sSup S ≤ B := by
  apply csSup_le hS_nonempty h_le

lemma nr_sup_norms_le_sup_re
    (h_nonempty : (numericalRange A).Nonempty)
    (h_circ : ∀ w : ℂ, ‖w‖ = 1 → (w • ·) '' numericalRange A = numericalRange A) :
    sSup (nrNorms A) ≤ sSup (nrRe A) := by
  apply nr_sup_le_of_forall_le (nrNorms A) (sSup (nrRe A))
  · exact nr_norm_set_nonempty h_nonempty
  · intro r hr
    exact nr_norm_elt_le_sup_re r hr h_circ

lemma numericalRadius_le_sup_re (h_nonempty : (numericalRange A).Nonempty)
    (h_circ : ∀ w : ℂ, ‖w‖ = 1 → (w • ·) '' numericalRange A = numericalRange A) :
    numericalRadius A ≤ sSup (Complex.re '' numericalRange A) := by
  rw [radius_eq_sup_norms]
  have h_set_eq : nrRe A = Complex.re '' numericalRange A := rfl
  rw [← h_set_eq]
  exact nr_sup_norms_le_sup_re h_nonempty h_circ

lemma rot_to_real_exists_w (z : ℂ) (_hz : z ≠ 0) :
    ∃ w : ℂ, w = (‖z‖ : ℂ) / z := by
  use (‖z‖ : ℂ) / z

lemma rot_to_real_w_unit (z : ℂ) (hz : z ≠ 0) :
    let w := (‖z‖ : ℂ) / z
    ‖w‖ = 1 := by
  intro w
  simp [w]
  aesop 

lemma rot_to_real_re_eq_norm (z : ℂ) (hz : z ≠ 0) :
    let w := (‖z‖ : ℂ) / z
    (w * z).re = ‖z‖ := by
  intro w
  have h1 : w * z = ‖z‖ := by
    simp [w]
    aesop
  rw [h1]
  simp

lemma rot_preserves_range (z : ℂ) (hz_mem : z ∈ numericalRange A)
    (w : ℂ) (hw : ‖w‖ = 1)
    (h_circ : ∀ u : ℂ, ‖u‖ = 1 → (u • ·) '' numericalRange A = numericalRange A) :
    w * z ∈ numericalRange A := by
  have h_img := h_circ w hw
  have h_mem : w • z ∈ (w • ·) '' numericalRange A := Set.mem_image_of_mem _ hz_mem
  rw [h_img] at h_mem
  simp [smul_eq_mul] at h_mem
  exact h_mem

lemma rotated_point_mem_re_set (z : ℂ) (hz_mem : z ∈ numericalRange A)
    (w : ℂ) (hw : ‖w‖ = 1)
    (h_circ : ∀ u : ℂ, ‖u‖ = 1 → (u • ·) '' numericalRange A = numericalRange A) :
    (w * z).re ∈ nrRe A := by
  let z' := w * z
  have h_mem : z' ∈ numericalRange A := rot_preserves_range z hz_mem w hw h_circ
  use z'

lemma norm_mem_nrRe_of_circular (z : ℂ) (hz : z ∈ numericalRange A)
    (h_circ : ∀ u : ℂ, ‖u‖ = 1 → (u • ·) '' numericalRange A = numericalRange A) :
    ‖z‖ ∈ nrRe A := by
  by_cases h0 : z = 0
  · subst h0; simp; use 0; simp [hz]
  · let w := (‖z‖ : ℂ) / z
    have hw : ‖w‖ = 1 := rot_to_real_w_unit z h0
    have hre : (w * z).re = ‖z‖ := rot_to_real_re_eq_norm z h0
    have h_in := rotated_point_mem_re_set z hz w hw h_circ
    rw [hre] at h_in
    exact h_in
  
lemma nrNorms_subset_nrRe
    (h_circ : ∀ u : ℂ, ‖u‖ = 1 → (u • ·) '' numericalRange A = numericalRange A) :
    nrNorms A ⊆ nrRe A := by
  intro r hr
  rcases hr with ⟨z, hz, rfl⟩
  exact norm_mem_nrRe_of_circular z hz h_circ

lemma sup_le_sup_of_subset {S T : Set ℝ} (h_sub : S ⊆ T)
    (hT_bdd : BddAbove T) (hS_nonempty : S.Nonempty) :
    sSup S ≤ sSup T := by
  apply csSup_le_csSup hT_bdd hS_nonempty h_sub

lemma nrRe_bdd_above_explicit : BddAbove (nrRe A) := nr_re_set_bdd_above

lemma nrNorms_sup_le_nrRe_sup (h_nonempty : (numericalRange A).Nonempty)
    (h_circ : ∀ u : ℂ, ‖u‖ = 1 → (u • ·) '' numericalRange A = numericalRange A) :
    sSup (nrNorms A) ≤ sSup (nrRe A) := by
  apply sup_le_sup_of_subset
  · exact nrNorms_subset_nrRe h_circ
  · exact nrRe_bdd_above_explicit
  · exact nr_norm_set_nonempty h_nonempty

lemma z_re_le_z_norm (z : ℂ) : z.re ≤ ‖z‖ := Complex.re_le_norm z

lemma z_norm_mem_nrNorms (z : ℂ) (hz : z ∈ numericalRange A) : ‖z‖ ∈ nrNorms A := by
  use z

lemma nrNorms_bdd_above_explicit : BddAbove (nrNorms A) := nr_norms_bdd_above

lemma z_norm_le_sup_nrNorms (z : ℂ) (hz : z ∈ numericalRange A) :
    ‖z‖ ≤ sSup (nrNorms A) := by
  apply le_csSup nrNorms_bdd_above_explicit
  exact z_norm_mem_nrNorms z hz

lemma z_re_le_sup_nrNorms (z : ℂ) (hz : z ∈ numericalRange A) :
    z.re ≤ sSup (nrNorms A) := by
  apply (z_re_le_z_norm z).trans
  exact z_norm_le_sup_nrNorms z hz

lemma nrRe_sup_le_nrNorms_sup (h_nonempty : (numericalRange A).Nonempty) :
    sSup (nrRe A) ≤ sSup (nrNorms A) := by
  apply csSup_le
  · exact nr_re_set_nonempty h_nonempty
  · intro r hr
    rcases hr with ⟨z, hz, rfl⟩
    exact z_re_le_sup_nrNorms z hz

lemma nrNorms_sup_eq_nrRe_sup (h_nonempty : (numericalRange A).Nonempty)
    (h_circ : ∀ u : ℂ, ‖u‖ = 1 → (u • ·) '' numericalRange A = numericalRange A) :
    sSup (nrNorms A) = sSup (nrRe A) := by
  apply le_antisymm
  · exact nrNorms_sup_le_nrRe_sup h_nonempty h_circ
  · exact nrRe_sup_le_nrNorms_sup h_nonempty

lemma radius_is_sup_nrNorms : numericalRadius A = sSup (nrNorms A) := rfl

lemma nrRe_is_complex_re_image : nrRe A = Complex.re '' numericalRange A := rfl

lemma numericalRadius_eq_sup_re_of_circular
    (A : E →L[ℂ] E)
    (h_circ : ∀ z : ℂ, ‖z‖ = 1 → (z • ·) '' numericalRange A = numericalRange A)
    (h_nonempty : (numericalRange A).Nonempty) :
    numericalRadius A = sSup (Complex.re '' numericalRange A) := by
  rw [radius_is_sup_nrNorms, ← nrRe_is_complex_re_image]
  exact nrNorms_sup_eq_nrRe_sup h_nonempty h_circ

section CrabbRadiusProof

lemma s01_n_pos (hn : n ≥ 2) : 0 < n := by
  omega

lemma s02_n_ge_one (hn : n ≥ 2) : n ≥ 1 := by
  omega

lemma s03_crabb_range_nonempty (hn : n ≥ 2) :
    (numericalRange (crabbCLM n)).Nonempty := by
  apply s5_11_range_nonempty (s01_n_pos hn)

lemma s04_crabb_circ_symm (hn : n ≥ 2) :
    ∀ z : ℂ, ‖z‖ = 1 → (z • ·) '' numericalRange (crabbCLM n) = numericalRange (crabbCLM n) := by
  exact crabb_numericalRange_circular (s02_n_ge_one hn)

lemma s05_crabb_radius_eq_sup_re (hn : n ≥ 2) :
    numericalRadius (crabbCLM n) = sSup (Complex.re '' numericalRange (crabbCLM n)) := by
  apply numericalRadius_eq_sup_re_of_circular
  · exact s04_crabb_circ_symm hn
  · exact s03_crabb_range_nonempty hn

lemma s06_re_inner_crabb_eq_herm (x : Euc n) :
    (⟪crabbCLM n x, x⟫).re = (⟪hermitianCLM n x, x⟫).re := by
  rw [inner_eq_real_part]

lemma s07_herm_inner_is_real_val (x : Euc n) :
    ⟪hermitianCLM n x, x⟫ = (⟪hermitianCLM n x, x⟫).re := by
  rw [hermitianCLM_inner_real]
  simp

lemma s08_re_crabb_subset_re_herm (_hn : n ≥ 2) :
    Complex.re '' numericalRange (crabbCLM n) ⊆ Complex.re '' numericalRange (hermitianCLM n) := by
  intro r hr
  rcases hr with ⟨z, hz, rfl⟩
  rcases hz with ⟨x, hx, rfl⟩
  use ⟪hermitianCLM n x, x⟫
  constructor
  · exact mem_numericalRange_of_unit (A := hermitianCLM n) hx
  · rw [s06_re_inner_crabb_eq_herm x]

lemma s09_re_herm_subset_re_crabb (_hn : n ≥ 2) :
    Complex.re '' numericalRange (hermitianCLM n) ⊆ Complex.re '' numericalRange (crabbCLM n) := by
  intro r hr
  rcases hr with ⟨z, hz, rfl⟩
  rcases hz with ⟨x, hx, rfl⟩
  use ⟪crabbCLM n x, x⟫
  constructor
  · exact mem_numericalRange_of_unit (A := crabbCLM n) hx
  · rw [s06_re_inner_crabb_eq_herm x]

lemma s10_re_range_eq (hn : n ≥ 2) :
    Complex.re '' numericalRange (crabbCLM n) = Complex.re '' numericalRange (hermitianCLM n) := by
  apply Set.Subset.antisymm
  · exact s08_re_crabb_subset_re_herm hn
  · exact s09_re_herm_subset_re_crabb hn

lemma s11_herm_opNorm_one (hn : n ≥ 2) :
    ‖hermitianCLM n‖ = 1 := by
  exact opNorm_hermitianCLM_eq_one hn

lemma s12_herm_re_le_norm_vec (hn : n ≥ 2) (x : Euc n) (hx : ‖x‖ = 1) :
    (⟪hermitianCLM n x, x⟫).re ≤ 1 := by
  have h_bound := re_inner_hermitianCLM_le_opNorm n hx
  rw [s11_herm_opNorm_one hn] at h_bound
  exact h_bound
  
lemma s13_re_herm_range_le_one (hn : n ≥ 2) :
    ∀ r ∈ Complex.re '' numericalRange (hermitianCLM n), r ≤ 1 := by
  intro r hr
  rcases hr with ⟨z, hz, rfl⟩
  rcases hz with ⟨x, hx, rfl⟩
  exact s12_herm_re_le_norm_vec hn x hx

lemma s14_sup_re_herm_le_one (hn : n ≥ 2) :
    sSup (Complex.re '' numericalRange (hermitianCLM n)) ≤ 1 := by
  apply csSup_le
  · exact range_re_nonempty (step5_lemma1_range_nonempty_of_pos n (s01_n_pos hn) _)
  · exact s13_re_herm_range_le_one hn

lemma s15_exists_eigen_one (hn : n ≥ 2) :
    ∃ x : Euc n, ‖x‖ = 1 ∧ ⟪hermitianCLM n x, x⟫ = 1 := by
  rcases hermitian_has_eigenvalue_one hn with ⟨x, hx_norm, hx_eq⟩
  use x, hx_norm
  rw [hx_eq, inner_self_eq_norm_sq_to_K]
  simp [hx_norm]

lemma s16_one_mem_re_herm (hn : n ≥ 2) :
    1 ∈ Complex.re '' numericalRange (hermitianCLM n) := by
  rcases s15_exists_eigen_one hn with ⟨x, hx_norm, hx_val⟩
  use 1
  constructor
  · rw [← hx_val]
    exact hermitianCLM_numRange_mem n hx_norm
  · simp

lemma s17_one_le_sup_re_herm (hn : n ≥ 2) :
    1 ≤ sSup (Complex.re '' numericalRange (hermitianCLM n)) := by
  apply le_csSup
  · apply nr_re_bdd_above_by_radius
    exact step5_lemma1_range_nonempty_of_pos n (s01_n_pos hn) _
  · exact s16_one_mem_re_herm hn

lemma s18_sup_re_herm_eq_one (hn : n ≥ 2) :
    sSup (Complex.re '' numericalRange (hermitianCLM n)) = 1 := by
  apply le_antisymm
  · exact s14_sup_re_herm_le_one hn
  · exact s17_one_le_sup_re_herm hn

lemma s19_sup_re_crabb_eq_one (hn : n ≥ 2) :
    sSup (Complex.re '' numericalRange (crabbCLM n)) = 1 := by
  rw [s10_re_range_eq hn]
  exact s18_sup_re_herm_eq_one hn

lemma s20_crabb_radius_eq_one (hn : n ≥ 2) :
    numericalRadius (crabbCLM n) = 1 := by
  rw [s05_crabb_radius_eq_sup_re hn]
  exact s19_sup_re_crabb_eq_one hn

lemma s21_norm_set_eq_radius_def (A : Euc n →L[ℂ] Euc n) :
    sSup { norm z | z ∈ numericalRange A } = numericalRadius A := by
  rw [numericalRadius]
  congr
  ext r
  constructor
  · rintro ⟨z, hz, rfl⟩
    use z, hz
  · rintro ⟨z, hz, rfl⟩
    use z, hz

theorem crabb_numerical_radius (hn : n ≥ 2) :
    sSup { norm z | z ∈ numericalRange (crabbCLM n) } = 1 := by
  rw [s21_norm_set_eq_radius_def]
  exact s20_crabb_radius_eq_one hn

lemma crabb_clm_pow_eq_matrix_pow (n : ℕ) (k : ℕ) :
    (crabbCLM n) ^ k = 
    (Matrix.toEuclideanLin (CrabbMatrix n ^ k)).toContinuousLinearMap := by
  induction k with
  | zero =>
    simp only [pow_zero]
    ext
    simp []
  | succ k ih =>
    simp only [pow_succ, ih]
    ext v
    simp only [crabbCLM, ContinuousLinearMap.mul_apply]
    aesop

lemma s23_norm_crabb_pow_eq_two (hn : n ≥ 2) : 
  ‖(crabbCLM n) ^ (n - 1)‖ = 2 := by
  rw [crabb_clm_pow_eq_matrix_pow]
  exact crabb_poly_norm_eq_two hn

lemma d01_poly_def (n : ℕ) : 
    (Polynomial.X : Polynomial ℂ) ^ (n - 1) = Polynomial.X ^ (n - 1) := rfl

lemma d02_poly_eval (n : ℕ) (z : ℂ) :
    (Polynomial.X ^ (n - 1)).eval z = z ^ (n - 1) := by
  simp only [Polynomial.eval_pow, Polynomial.eval_X]

lemma d03_norm_poly_eval (n : ℕ) (z : ℂ) :
    ‖(Polynomial.X ^ (n - 1)).eval z‖ = ‖z‖ ^ (n - 1) := by
  rw [d02_poly_eval]
  exact Complex.norm_pow z (n - 1)

lemma d04_exponent_pos (hn : n ≥ 2) : 
    0 < n - 1 := by
  omega

lemma d05_radius_set_def (n : ℕ) :
    { norm z | z ∈ numericalRange (crabbCLM n) } = 
    (norm) '' numericalRange (crabbCLM n) := by
  ext r
  simp only [Set.mem_image, Set.mem_setOf_eq]

lemma d06_target_set_def (n : ℕ) :
    { ‖(Polynomial.X ^ (n - 1)).eval z‖ | z ∈ numericalRange (crabbCLM n) } =
    (fun r => r ^ (n - 1)) '' { norm z | z ∈ numericalRange (crabbCLM n) } := by
  ext y
  simp only [Set.mem_image, Set.mem_setOf_eq, d03_norm_poly_eval]
  constructor
  · rintro ⟨z, hz, rfl⟩
    use ‖z‖
    constructor
    · use z, hz
    · rfl
  · rintro ⟨r, ⟨z, hz, rfl⟩, rfl⟩
    use z, hz

lemma d07_radius_sup_eq_one (hn : n ≥ 2) :
    sSup { norm z | z ∈ numericalRange (crabbCLM n) } = 1 := by
  exact crabb_numerical_radius hn

lemma d08_radius_mem_le_one (hn : n ≥ 2) (r : ℝ) 
    (hr : r ∈ { norm z | z ∈ numericalRange (crabbCLM n) }) : 
    r ≤ 1 := by
  have h_sup := d07_radius_sup_eq_one hn
  rw [← h_sup]
  apply le_csSup
  · convert nr_norms_bdd_above (A := crabbCLM n)
    ext r
    simp [nrNorms]
    aesop
  · exact hr

lemma d09_radius_nonneg (r : ℝ) 
    (hr : r ∈ { norm z | z ∈ numericalRange (crabbCLM n) }) : 
    0 ≤ r := by
  rcases hr with ⟨z, _, rfl⟩
  exact norm_nonneg z

lemma d10_target_mem_le_one (hn : n ≥ 2) (y : ℝ)
    (hy : y ∈ { ‖(Polynomial.X ^ (n - 1)).eval z‖ | z ∈ numericalRange (crabbCLM n) }) :
    y ≤ 1 := by
  rw [d06_target_set_def] at hy
  rcases hy with ⟨r, hr_in, rfl⟩
  have h_le := d08_radius_mem_le_one hn r hr_in
  have h_pos := d09_radius_nonneg r hr_in
  apply pow_le_one₀
  · exact h_pos
  · exact h_le

lemma d11_target_bdd_above (hn : n ≥ 2) :
    BddAbove { ‖(Polynomial.X ^ (n - 1)).eval z‖ | z ∈ numericalRange (crabbCLM n) } := by
  use 1
  intro y hy
  exact d10_target_mem_le_one hn y hy

lemma d12_target_nonempty (hn : n ≥ 2) :
    { ‖(Polynomial.X ^ (n - 1)).eval z‖ | z ∈ numericalRange (crabbCLM n) }.Nonempty := by
  have h := s03_crabb_range_nonempty hn
  rcases h with ⟨z, hz⟩
  use ‖(Polynomial.X ^ (n - 1)).eval z‖
  use z, hz

lemma d13_sup_target_le_one (hn : n ≥ 2) :
    sSup { ‖(Polynomial.X ^ (n - 1)).eval z‖ | z ∈ numericalRange (crabbCLM n) } ≤ 1 := by
  apply csSup_le
  · exact d12_target_nonempty hn
  · intro y hy
    exact d10_target_mem_le_one hn y hy

lemma d14_exists_radius_close_to_one (hn : n ≥ 2) (ε : ℝ) (hε : ε > 0) :
    ∃ r ∈ { norm z | z ∈ numericalRange (crabbCLM n) }, 1 - ε < r := by
  let S := { norm z | z ∈ numericalRange (crabbCLM n) }
  have h_sup : sSup S = 1 := d07_radius_sup_eq_one hn
  have h_nonempty : S.Nonempty := by
    rcases s03_crabb_range_nonempty hn with ⟨z, hz⟩
    use ‖z‖
    use z, hz
  have h_lt : 1 - ε < sSup S := by
    rw [h_sup]
    linarith
  exact exists_lt_of_lt_csSup h_nonempty h_lt

lemma d15_exponent_pos (hn : n ≥ 2) : 
    0 < n - 1 := by
  omega

lemma d16_pow_mono (hn : n ≥ 2) (a b : ℝ) (h_nonneg : 0 ≤ a) (h_lt : a < b) : 
    a ^ (n - 1) < b ^ (n - 1) := by
  have h_exp_pos : 0 < n - 1 := by omega
  have h_b_pos : 0 < b := by linarith
  apply pow_lt_pow_left₀ h_lt h_nonneg h_exp_pos.ne'

lemma b01_n_ge_one (hn : n ≥ 2) : 1 ≤ n := by
  omega

lemma b02_cast_n_sub_one_eq (hn : n ≥ 2) : 
    ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
  rw [Nat.cast_sub]
  · simp
  · exact b01_n_ge_one hn

lemma b03_neg_epsilon_ge_neg_one (ε : ℝ) (hε_small : ε ≤ 1) : 
    -1 ≤ -ε := by
  linarith

lemma b04_bernoulli_raw (k : ℕ) (x : ℝ) (hx : -1 ≤ x) : 
    1 + (k : ℝ) * x ≤ (1 + x) ^ k := by
  have h_bound : -2 ≤ x := by linarith
  exact one_add_mul_le_pow h_bound k

lemma b05_apply_bernoulli_to_neg_epsilon_strict (n : ℕ) (_hn : n ≥ 2) (ε : ℝ) (hε_small : ε ≤ 1) : 
    1 + ((n - 1 : ℕ) : ℝ) * (-ε) ≤ (1 + -ε) ^ (n - 1) := by
  apply b04_bernoulli_raw (n - 1) (-ε)
  linarith

lemma b05_apply_bernoulli_to_neg_epsilon (_hn : n ≥ 2) (ε : ℝ) (hε_small : ε ≤ 1) : 
    1 + ((n - 1 : ℕ) : ℝ) * (-ε) ≤ (1 + -ε) ^ (n - 1) := by
  apply b04_bernoulli_raw
  exact b03_neg_epsilon_ge_neg_one ε hε_small

lemma b06_mul_neg_comm (a b : ℝ) : 
    a * (-b) = -(a * b) := by
  ring

lemma b07_one_add_neg_eq_sub (a b : ℝ) : 
    a + -b = a - b := by
  ring

lemma b08_lhs_algebra_step1 (_hn : n ≥ 2) (ε : ℝ) :
    1 + ((n - 1 : ℕ) : ℝ) * (-ε) = 1 - ((n - 1 : ℕ) : ℝ) * ε := by
  rw [b06_mul_neg_comm, b07_one_add_neg_eq_sub]

lemma b09_lhs_cast_step (hn : n ≥ 2) (ε : ℝ) :
    1 - ((n - 1 : ℕ) : ℝ) * ε = 1 - ((n : ℝ) - 1) * ε := by
  rw [b02_cast_n_sub_one_eq hn]

lemma b10_lhs_eq_target (hn : n ≥ 2) (ε : ℝ) :
    1 + ((n - 1 : ℕ) : ℝ) * (-ε) = 1 - ((n : ℝ) - 1) * ε := by
  rw [b08_lhs_algebra_step1 hn, b09_lhs_cast_step hn]

lemma b11_rhs_base_algebra (ε : ℝ) : 
    1 + -ε = 1 - ε := by
  ring

lemma b12_rhs_eq_target (n : ℕ) (ε : ℝ) :
    (1 + -ε) ^ (n - 1) = (1 - ε) ^ (n - 1) := by
  rw [b11_rhs_base_algebra]

lemma d17_bernoulli_bound
    (n : ℕ) (hn : n ≥ 2) 
    (ε : ℝ) (_hε_nonneg : 0 ≤ ε) (hε_small : ε ≤ 1) :
    1 - ((n : ℝ) - 1) * ε ≤ (1 - ε) ^ (n - 1) := by
  have h_raw :
      1 + ((n - 1 : ℕ) : ℝ) * (-ε) ≤ (1 + -ε) ^ (n - 1) :=
    b05_apply_bernoulli_to_neg_epsilon (n := n) hn ε hε_small
  have := h_raw
  rw [b10_lhs_eq_target hn, b12_rhs_eq_target] at h_raw
  exact h_raw

lemma d18_epsilon_selection (n : ℕ) (hn : n ≥ 2) (δ : ℝ) (hδ : δ > 0) :
    ∃ ε : ℝ, ε > 0 ∧ ε ≤ 1 ∧ (n - 1 : ℝ) * ε < δ := by
  let N := (n - 1 : ℝ)
  have hN : N > 0 := by
    have h_cast : (n : ℝ) ≥ 2 := by exact_mod_cast hn
    simp only [N]
    linarith
  use min 1 (δ / (2 * N))
  constructor
  · apply lt_min
    · norm_num
    · apply div_pos hδ
      linarith
  constructor
  · exact min_le_left _ _
  · calc
      N * min 1 (δ / (2 * N)) ≤ N * (δ / (2 * N)) := 
          mul_le_mul_of_nonneg_left (min_le_right _ _) (le_of_lt hN)
      _ = δ / 2 := by field_simp [hN.ne']
      _ < δ := by linarith

lemma d19_elem_close_to_one_pow (n : ℕ) (hn : n ≥ 2) (δ : ℝ) (hδ : δ > 0) :
    ∃ y ∈ { ‖(Polynomial.X ^ (n - 1)).eval z‖ | z ∈ numericalRange (crabbCLM n) }, 
    1 - δ < y := by
  rcases d18_epsilon_selection n hn δ hδ with ⟨ε, hε_pos, hε_le_one, h_bound⟩
  rcases d14_exists_radius_close_to_one hn ε hε_pos with ⟨r, hr_mem, hr_lt⟩
  use r ^ (n - 1)
  constructor
  · rw [d06_target_set_def]
    exact Set.mem_image_of_mem _ hr_mem
  · calc
      1 - δ < 1 - (n - 1 : ℝ) * ε := by linarith
      _ ≤ (1 - ε) ^ (n - 1) := d17_bernoulli_bound n hn ε (le_of_lt hε_pos) hε_le_one
      _ < r ^ (n - 1) := by
        apply d16_pow_mono hn
        · linarith [hε_le_one]
        · exact hr_lt

lemma d20_sup_target_ge_approx (hn : n ≥ 2) (δ : ℝ) (hδ : δ > 0) :
    1 - δ ≤ sSup { ‖(Polynomial.X ^ (n - 1)).eval z‖ | z ∈ numericalRange (crabbCLM n) } := by
  rcases d19_elem_close_to_one_pow n hn δ hδ with ⟨y, hy_mem, hy_val⟩
  apply le_csSup_of_le
  · exact d11_target_bdd_above hn
  · exact hy_mem
  · exact le_of_lt hy_val

lemma d21_sup_target_ge_one (hn : n ≥ 2) :
    1 ≤ sSup { ‖(Polynomial.X ^ (n - 1)).eval z‖ | z ∈ numericalRange (crabbCLM n) } := by
  apply le_of_forall_pos_le_add
  intro δ hδ
  have h_approx := d20_sup_target_ge_approx hn δ hδ
  linarith

lemma crabb_denominator_eq_one (hn : n ≥ 2) :
    let p : Polynomial ℂ := Polynomial.X ^ (n - 1)
    sSup { ‖p.eval z‖ | z ∈ numericalRange (crabbCLM n) } = 1 := by
  intro p
  apply le_antisymm
  · exact d13_sup_target_le_one hn
  · exact d21_sup_target_ge_one hn

theorem crabb_witnesses_constant_two (hn : n ≥ 2) : 
  let p : Polynomial ℂ := Polynomial.X ^ (n - 1)
  ‖Polynomial.aeval (crabbCLM n) p‖ / sSup { ‖p.eval z‖ | z ∈ numericalRange (crabbCLM n) } = 2 := by
  intro p
  have h_eval : Polynomial.aeval (crabbCLM n) p = (crabbCLM n) ^ (n - 1) := by
    simp [p, Polynomial.aeval_X_pow]
  rw [h_eval]
  rw [crabb_clm_pow_eq_matrix_pow]
  rw [crabb_poly_norm_eq_two hn]
  rw [crabb_denominator_eq_one hn]
  norm_num

end CrabbRadiusProof

end NumericalRadiusCalculation

open Submodule

section SpanCollapse
abbrev E3 := EuclideanSpace ℂ (Fin 3)

noncomputable def hermPart (u : ℂ) (A : E3 →L[ℂ] E3) : E3 →L[ℂ] E3 :=
  (1 / 2 : ℂ) • (u • A + (star u) • A.adjoint)

lemma hermPart_apply (A : E3 →L[ℂ] E3) (u : ℂ) (x : E3) :
    hermPart u A x = (1 / 2 : ℂ) • (u • (A x) + (star u) • (A.adjoint x)) := by
  simp [hermPart, smul_add, smul_smul]

lemma two_mul_one_half : (2 : ℂ) * (1 / 2 : ℂ) = 1 := by
  norm_num

lemma two_smul_half (v : E3) : (2 : ℂ) • ((1 / 2 : ℂ) • v) = v := by
  simp [smul_smul]

lemma two_smul_hermPart (A : E3 →L[ℂ] E3) (u : ℂ) (x : E3) :
    (2 : ℂ) • (hermPart u A x) = u • (A x) + (star u) • (A.adjoint x) := by
  rw [hermPart_apply (A := A) (u := u) (x := x)]
  have h : (2 : ℂ) • ((1 / 2 : ℂ) • (u • (A x) + (star u) • (A.adjoint x))) = 
           u • (A x) + (star u) • (A.adjoint x) := two_smul_half (u • (A x) + (star u) • (A.adjoint x))
  simp [smul_add, smul_smul] at h ⊢

lemma eigen_eq_after_two_smul
    (A : E3 →L[ℂ] E3) (u : ℂ) (x : E3) (lam : ℂ)
    (h : hermPart u A x = lam • x) :
    (2 : ℂ) • (hermPart u A x) = (2 : ℂ) • (lam • x) := by
  simp [h]

lemma eigen_eq_uAx_add_conj_adjoint
    (A : E3 →L[ℂ] E3) (u : ℂ) (x : E3) (lam : ℂ)
    (h : hermPart u A x = lam • x) :
    u • (A x) + (star u) • (A.adjoint x) = (2 * lam) • x := by
  have h1 := eigen_eq_after_two_smul (A := A) (u := u) (x := x) (lam := lam) h
  rw [two_smul_hermPart (A := A) (u := u) (x := x)] at h1
  simpa [smul_smul, mul_assoc] using h1

lemma star_u_smul_adjoint_eq_sub
    (A : E3 →L[ℂ] E3) (u : ℂ) (x : E3) (lam : ℂ)
    (h : hermPart u A x = lam • x) :
    (star u) • (A.adjoint x) = (2 * lam) • x - u • (A x) := by
  have h1 : u • (A x) + (star u) • (A.adjoint x) = (2 * lam) • x := 
    eigen_eq_uAx_add_conj_adjoint (A := A) (u := u) (x := x) (lam := lam) h
  have h2 : (star u) • (A.adjoint x) + u • (A x) = (2 * lam) • x := by
    rw [add_comm]
    exact h1
  exact eq_sub_of_add_eq h2

lemma norm_eq_one_ne_zero {u : ℂ} (hu : ‖u‖ = 1) : u ≠ 0 := by
  intro h0
  subst h0
  simp at hu

lemma star_ne_zero_of_ne_zero {u : ℂ} (hu : u ≠ 0) : star u ≠ 0 := by
  intro hs
  apply hu
  have := congrArg star hs
  simpa using this

lemma star_ne_zero_of_norm_eq_one {u : ℂ} (hu : ‖u‖ = 1) : star u ≠ 0 :=
  star_ne_zero_of_ne_zero (norm_eq_one_ne_zero hu)

lemma inv_smul_smul_cancel {a : ℂ} (ha : a ≠ 0) (v : E3) :
    a⁻¹ • (a • v) = v := by
  simp [smul_smul, ha]

lemma adjoint_eq_combo
    (A : E3 →L[ℂ] E3) (u : ℂ) (x : E3) (lam : ℂ)
    (hu : ‖u‖ = 1)
    (h : hermPart u A x = lam • x) :
    A.adjoint x = (star u)⁻¹ • ((2 * lam) • x - u • (A x)) := by
  have hs : (star u) • (A.adjoint x) = (2 * lam) • x - u • (A x) :=
    star_u_smul_adjoint_eq_sub (A := A) (u := u) (x := x) (lam := lam) h
  have hsu0 : star u ≠ 0 := star_ne_zero_of_norm_eq_one hu
  calc
    A.adjoint x = (star u)⁻¹ • ((star u) • (A.adjoint x)) := by
      rw [← inv_smul_smul_cancel hsu0 (A.adjoint x)]
      aesop
    _ = (star u)⁻¹ • ((2 * lam) • x - u • (A x)) := by
      rw [hs]

abbrev spanXA (A : E3 →L[ℂ] E3) (x : E3) : Submodule ℂ E3 :=
  Submodule.span ℂ ({x, A x} : Set E3)

lemma x_mem_spanXA (A : E3 →L[ℂ] E3) (x : E3) :
    x ∈ spanXA A x := by
  exact Submodule.subset_span (by simp [])

lemma Ax_mem_spanXA (A : E3 →L[ℂ] E3) (x : E3) :
    A x ∈ spanXA A x := by
  exact Submodule.subset_span (by simp [])

lemma smul_mem_spanXA {A : E3 →L[ℂ] E3} {x v : E3} (c : ℂ)
    (hv : v ∈ spanXA A x) :
    c • v ∈ spanXA A x := by
  exact Submodule.smul_mem _ c hv

lemma add_mem_spanXA {A : E3 →L[ℂ] E3} {x v w : E3}
    (hv : v ∈ spanXA A x) (hw : w ∈ spanXA A x) :
    v + w ∈ spanXA A x := by
  exact Submodule.add_mem _ hv hw

lemma sub_mem_spanXA {A : E3 →L[ℂ] E3} {x v w : E3}
    (hv : v ∈ spanXA A x) (hw : w ∈ spanXA A x) :
    v - w ∈ spanXA A x := by
  simpa [sub_eq_add_neg] using
    add_mem_spanXA (A := A) (x := x) hv (smul_mem_spanXA (A := A) (x := x) (-1 : ℂ) hw)

lemma smul_x_mem_spanXA (A : E3 →L[ℂ] E3) (x : E3) (c : ℂ) :
    c • x ∈ spanXA A x :=
  smul_mem_spanXA (A := A) (x := x) c (x_mem_spanXA A x)

lemma smul_Ax_mem_spanXA (A : E3 →L[ℂ] E3) (x : E3) (c : ℂ) :
    c • (A x) ∈ spanXA A x :=
  smul_mem_spanXA (A := A) (x := x) c (Ax_mem_spanXA A x)

lemma rhs_mem_spanXA
    (A : E3 →L[ℂ] E3) (u : ℂ) (x : E3) (lam : ℂ) :
    ((2 * lam) • x - u • (A x)) ∈ spanXA A x := by
  exact sub_mem_spanXA (A := A) (x := x)
    (smul_x_mem_spanXA (A := A) (x := x) (2 * lam))
    (smul_Ax_mem_spanXA (A := A) (x := x) u)

lemma scaled_rhs_mem_spanXA
    (A : E3 →L[ℂ] E3) (u : ℂ) (x : E3) (lam : ℂ) :
    (star u)⁻¹ • ((2 * lam) • x - u • (A x)) ∈ spanXA A x := by
  exact smul_mem_spanXA (A := A) (x := x) (star u)⁻¹ (rhs_mem_spanXA A u x lam)

lemma adjoint_mem_span_of_eigen_hermPart
    (A : E3 →L[ℂ] E3) (u : ℂ) (x : E3) (lam : ℂ)
    (hu : ‖u‖ = 1)
    (h : hermPart u A x = lam • x) :
    A.adjoint x ∈ Submodule.span ℂ ({x, A x} : Set E3) := by
  have hx : A.adjoint x = (star u)⁻¹ • ((2 * lam) • x - u • (A x)) :=
    adjoint_eq_combo (A := A) (u := u) (x := x) (lam := lam) hu h
  simpa [spanXA] using (hx ▸ scaled_rhs_mem_spanXA (A := A) (u := u) (x := x) (lam := lam))

end SpanCollapse

section DeterminantC

noncomputable def Aclm (A : Matrix (Fin 3) (Fin 3) ℂ) : E3 →L[ℂ] E3 :=
  (Matrix.toEuclideanLin A).toContinuousLinearMap

lemma Aclm_apply (A : Matrix (Fin 3) (Fin 3) ℂ) (x : E3) :
    Aclm A x = (Matrix.toEuclideanLin A).toContinuousLinearMap x := rfl

lemma Aclm_adjoint_apply (A : Matrix (Fin 3) (Fin 3) ℂ) (x : E3) :
    (Aclm A).adjoint x = (Matrix.toEuclideanLin A).toContinuousLinearMap.adjoint x := rfl


lemma adjoint_mem_span_two
    (A : Matrix (Fin 3) (Fin 3) ℂ) (x : E3) (u : ℂ) (lam : ℂ)
    (hu : ‖u‖ = 1)
    (h_eig : hermPart u (Aclm A) x = lam • x) :
    (Aclm A).adjoint x ∈ Submodule.span ℂ ({x, (Aclm A) x} : Set E3) := by
  simpa using
    (adjoint_mem_span_of_eigen_hermPart (A := (Aclm A)) (u := u) (x := x) (lam := lam) hu h_eig)

lemma mem_span_pair_iff_exists (v x y : E3) :
    v ∈ Submodule.span ℂ ({x, y} : Set E3) →
    ∃ a b : ℂ, v = a • x + b • y := by
  intro hv
  classical
  rcases (Submodule.mem_span_pair).1 hv with ⟨a, b, rfl⟩
  exact ⟨a, b, rfl⟩

lemma adjoint_eq_linear_combo
    (A : Matrix (Fin 3) (Fin 3) ℂ) (x : E3) (u : ℂ) (lam : ℂ)
    (hu : ‖u‖ = 1)
    (h_eig : hermPart u (Aclm A) x = lam • x) :
    ∃ a b : ℂ, (Aclm A).adjoint x = a • x + b • ((Aclm A) x) := by
  have hspan := adjoint_mem_span_two (A := A) (x := x) (u := u) (lam := lam) hu h_eig
  exact mem_span_pair_iff_exists ((Aclm A).adjoint x) x ((Aclm A) x) hspan

noncomputable def colMat (x y z : E3) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => ![x, y, z] j i

lemma colMat_apply (x y z : E3) (i j : Fin 3) :
    colMat x y z i j = (![x, y, z] j) i := by
  simp [colMat]

lemma colMat_col0 (x y z : E3) :
    (colMat x y z).col 0 = x := by
  ext i
  simp [Matrix.col, colMat_apply]

lemma colMat_col1 (x y z : E3) :
    (colMat x y z).col 1 = y := by
  ext i
  simp [Matrix.col, colMat_apply]

lemma colMat_col2 (x y z : E3) :
    (colMat x y z).col 2 = z := by
  ext i
  simp [Matrix.col, colMat_apply]

noncomputable def literalMat (x y z : E3) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![x 0, y 0, z 0;
    x 1, y 1, z 1;
    x 2, y 2, z 2]

lemma literal_eq_colMat (x y z : E3) :
    literalMat x y z = colMat x y z := by
  classical
  ext i j
  fin_cases i <;> fin_cases j <;> simp [literalMat, colMat]

lemma det_literal_eq_det_colMat (x y z : E3) :
    Matrix.det (literalMat x y z) = Matrix.det (colMat x y z) := by
  simp [literal_eq_colMat]

noncomputable def coeffVec (a b : ℂ) : (Fin 3 → ℂ) :=
  ![-a, -b, 1]

lemma coeffVec_ne_zero (a b : ℂ) : coeffVec a b ≠ 0 := by
  intro h
  have : (coeffVec a b) 2 = 0 := by simp [h]
  simp [coeffVec] at this

lemma mulVec_fin3_paren (M : Matrix (Fin 3) (Fin 3) ℂ) (v : Fin 3 → ℂ) (i : Fin 3) :
    M.mulVec v i = M i 0 * v 0 + (M i 1 * v 1 + M i 2 * v 2) := by
  classical
  change (∑ j : Fin 3, M i j * v j) = _
  simp [Fin.sum_univ_three, add_assoc]

lemma mulVec_fin3 (M : Matrix (Fin 3) (Fin 3) ℂ) (v : Fin 3 → ℂ) (i : Fin 3) :
    M.mulVec v i = M i 0 * v 0 + M i 1 * v 1 + M i 2 * v 2 := by
  simpa [add_assoc] using (mulVec_fin3_paren (M := M) (v := v) (i := i))

lemma colMat_entry0 (x y z : E3) (i : Fin 3) :
    colMat x y z i 0 = x i := by
  classical
  simp [colMat]

lemma colMat_entry1 (x y z : E3) (i : Fin 3) :
    colMat x y z i 1 = y i := by
  classical
  simp [colMat]

lemma colMat_entry2 (x y z : E3) (i : Fin 3) :
    colMat x y z i 2 = z i := by
  classical
  simp [colMat]

lemma colMat_mulVec_coeff_apply (x y z : E3) (a b : ℂ) (i : Fin 3) :
    (colMat x y z).mulVec (coeffVec a b) i
      = x i * (-a) + y i * (-b) + z i := by
  classical
  simp [mulVec_fin3,
        colMat_entry0, colMat_entry1, colMat_entry2,
        coeffVec,
        add_assoc, mul_comm]

lemma coord_of_combo (x y z : E3) (a b : ℂ) (hz : z = a • x + b • y) (i : Fin 3) :
    z i = a * x i + b * y i := by
  have h := congrArg (fun v : E3 => v i) hz
  simpa [smul_eq_mul, add_assoc, add_comm, add_left_comm] using h

lemma cancel_coord (xi yi zi a b : ℂ) (hzi : zi = a * xi + b * yi) :
    xi * (-a) + yi * (-b) + zi = 0 := by
  simp [hzi, mul_comm, add_assoc, add_comm]

lemma colMat_mulVec_coeff
    (x y z : E3) (a b : ℂ)
    (hz : z = a • x + b • y) :
    (colMat x y z).mulVec (coeffVec a b) = 0 := by
  ext i
  have hzi : z i = a * x i + b * y i := coord_of_combo x y z a b hz i
  simpa [colMat_mulVec_coeff_apply x y z a b i] using (cancel_coord (x i) (y i) (z i) a b hzi)

lemma isUnit_det_of_ne_zero (M : Matrix (Fin 3) (Fin 3) ℂ) (h : M.det ≠ 0) :
    IsUnit M.det :=
  isUnit_iff_ne_zero.mpr h

lemma inv_mul_eq_one_of_det_ne_zero (M : Matrix (Fin 3) (Fin 3) ℂ) (h : M.det ≠ 0) :
    M⁻¹ * M = 1 := by
  apply Matrix.nonsing_inv_mul
  exact isUnit_det_of_ne_zero M h

lemma mulVec_assoc_apply (A B : Matrix (Fin 3) (Fin 3) ℂ) (v : Fin 3 → ℂ) :
    (A * B).mulVec v = A.mulVec (B.mulVec v) := by
  simp [Matrix.mulVec_mulVec]

lemma one_mulVec_id (v : Fin 3 → ℂ) :
    (1 : Matrix (Fin 3) (Fin 3) ℂ).mulVec v = v := by
  simp [Matrix.one_mulVec]

lemma inv_mul_cancel_apply (M : Matrix (Fin 3) (Fin 3) ℂ) (v : Fin 3 → ℂ) (h : M.det ≠ 0) :
    M⁻¹.mulVec (M.mulVec v) = v := by
  rw [← mulVec_assoc_apply, inv_mul_eq_one_of_det_ne_zero M h, one_mulVec_id]

lemma mulVec_zero_apply (M : Matrix (Fin 3) (Fin 3) ℂ) :
    M.mulVec 0 = 0 := by
  exact map_zero (Matrix.toLin' M)

lemma eq_zero_of_det_ne_zero_mulVec_eq_zero
    (M : Matrix (Fin 3) (Fin 3) ℂ) (v : Fin 3 → ℂ)
    (hdet : M.det ≠ 0) (hv : M.mulVec v = 0) :
    v = 0 := by
  have h_cancel := inv_mul_cancel_apply M v hdet
  rw [hv, mulVec_zero_apply] at h_cancel
  exact h_cancel.symm

lemma det_eq_zero_of_exists_mulVec_eq_zero
    (M : Matrix (Fin 3) (Fin 3) ℂ) :
    (∃ v : (Fin 3 → ℂ), v ≠ 0 ∧ M.mulVec v = 0) → Matrix.det M = 0 := by
  intro h_exists
  rcases h_exists with ⟨v, v_ne, h_mul⟩
  by_contra h_det
  have v_eq_zero := eq_zero_of_det_ne_zero_mulVec_eq_zero M v h_det h_mul
  exact v_ne v_eq_zero

lemma det_colMat_eq_zero_of_combo
    (x y z : E3) :
    (∃ a b : ℂ, z = a • x + b • y) → Matrix.det (colMat x y z) = 0 := by
  rintro ⟨a, b, hz⟩
  apply det_eq_zero_of_exists_mulVec_eq_zero
  refine ⟨coeffVec a b, coeffVec_ne_zero a b, ?_⟩
  exact colMat_mulVec_coeff x y z a b hz

lemma det_eq_zero_of_boundary_point
    (A : Matrix (Fin 3) (Fin 3) ℂ)
    (x : E3)
    (u : ℂ) (lam : ℂ)
    (hu : ‖u‖ = 1)
    (h_eig : hermPart u (Aclm A) x = lam • x) :
    Matrix.det
      !![x 0, (Matrix.toEuclideanLin A x) 0, (Matrix.toEuclideanLin A).adjoint x 0;
        x 1, (Matrix.toEuclideanLin A x) 1, (Matrix.toEuclideanLin A).adjoint x 1;
        x 2, (Matrix.toEuclideanLin A x) 2, (Matrix.toEuclideanLin A).adjoint x 2] = 0 := by
  let y : E3 := (Aclm A) x
  let z : E3 := (Aclm A).adjoint x
  have hz_combo : ∃ a b : ℂ, z = a • x + b • y := by
    simpa [y, z] using adjoint_eq_linear_combo (A := A) (x := x) (u := u) (lam := lam) hu h_eig
  have : Matrix.det (colMat x y z) = 0 := det_colMat_eq_zero_of_combo x y z hz_combo
  simpa [det_literal_eq_det_colMat, literalMat, y, z, Aclm] using this

end DeterminantC

section SpanCoefficients

lemma exists_of_mem_span_pair {x y z : E3} (h : z ∈ Submodule.span ℂ ({x, y} : Set E3)) :
    ∃ a b : ℂ, z = a • x + b • y := by
  have := Submodule.mem_span_pair.mp h
  rcases this with ⟨a, b, rfl⟩
  exact ⟨a, b, rfl⟩

def vec2 (x y : E3) : Fin 2 → E3 := ![x, y]

lemma linear_combo_eq_finsum {x y : E3} (a b : ℂ) :
    a • x + b • y = ∑ i : Fin 2, (![a, b] i) • (![x, y] i) := by
  simp [Fin.sum_univ_two]

noncomputable def toFinsupp (a b : ℂ) : Fin 2 →₀ ℂ :=
  (Finsupp.equivFunOnFinite).symm ![a, b]

lemma toFinsupp_apply_zero (a b : ℂ) : (toFinsupp a b) 0 = a := by
  simp [toFinsupp]

lemma toFinsupp_apply_one (a b : ℂ) : (toFinsupp a b) 1 = b := by
  simp [toFinsupp]

noncomputable def coeff_fun (a b : ℂ) : Fin 2 → ℂ := ![a, b]
noncomputable def vec_fun (x y : E3) : Fin 2 → E3 := ![x, y]

lemma combo_eq_sum (x y : E3) (a b : ℂ) :
    a • x + b • y = ∑ i : Fin 2, (coeff_fun a b i) • (vec_fun x y i) := by
  simp [coeff_fun, vec_fun, Fin.sum_univ_two]

lemma fun_coeffs_eq_zero_of_indep {x y : E3}
    (h_indep : LinearIndependent ℂ (vec_fun x y))
    (a b : ℂ)
    (h_sum : a • x + b • y = 0) :
    coeff_fun a b = 0 := by
  rw [combo_eq_sum] at h_sum
  have h_forall_zero := linearIndependent_iff'.mp h_indep Finset.univ (coeff_fun a b) h_sum
  ext i
  exact h_forall_zero i (Finset.mem_univ i)

lemma a_eq_zero_of_fun_zero {a b : ℂ} (h : coeff_fun a b = 0) : a = 0 := by
  have h0 : coeff_fun a b 0 = 0 := congrFun h 0
  simpa [coeff_fun] using h0

lemma b_eq_zero_of_fun_zero {a b : ℂ} (h : coeff_fun a b = 0) : b = 0 := by
  have h1 : coeff_fun a b 1 = 0 := congrFun h 1
  simpa [coeff_fun] using h1

lemma independent_implies_zero_coeffs {x y : E3}
    (h_indep : LinearIndependent ℂ ![x, y])
    (a b : ℂ)
    (h_sum : a • x + b • y = 0) :
    a = 0 ∧ b = 0 := by
  have h_fun_zero := fun_coeffs_eq_zero_of_indep h_indep a b h_sum
  exact ⟨a_eq_zero_of_fun_zero h_fun_zero, b_eq_zero_of_fun_zero h_fun_zero⟩

lemma sub_smul_distrib (c d : ℂ) (v : E3) : c • v - d • v = (c - d) • v := by
  exact (sub_smul c d v).symm

lemma sub_combos_eq_diff_combo {x y : E3} {a b a' b' : ℂ} :
    (a • x + b • y) - (a' • x + b' • y) = (a - a') • x + (b - b') • y := by
  simp [add_sub_add_comm, sub_smul_distrib]

lemma diff_coeffs_eq_zero {x y : E3}
    (h_indep : LinearIndependent ℂ ![x, y])
    (a b a' b' : ℂ)
    (h_eq : a • x + b • y = a' • x + b' • y) :
    (a - a') = 0 ∧ (b - b') = 0 := by
  have h_diff_zero : (a - a') • x + (b - b') • y = 0 := by
    rw [← sub_combos_eq_diff_combo, sub_eq_zero_of_eq h_eq]
  exact independent_implies_zero_coeffs h_indep (a - a') (b - b') h_diff_zero

lemma eq_of_sub_eq_zero_scalar {c d : ℂ} (h : c - d = 0) : c = d :=
  sub_eq_zero.mp h

lemma coeffs_unique_of_combos_eq {x y : E3}
    (h_indep : LinearIndependent ℂ ![x, y])
    {a b a' b' : ℂ}
    (h_eq : a • x + b • y = a' • x + b' • y) :
    a = a' ∧ b = b' := by
  have h := diff_coeffs_eq_zero h_indep a b a' b' h_eq
  exact ⟨eq_of_sub_eq_zero_scalar h.1, eq_of_sub_eq_zero_scalar h.2⟩

lemma prod_unique_of_combos_eq {x y : E3}
    (h_indep : LinearIndependent ℂ ![x, y])
    (p q : ℂ × ℂ)
    (h_eq : p.1 • x + p.2 • y = q.1 • x + q.2 • y) :
    p = q := by
  have h := coeffs_unique_of_combos_eq h_indep h_eq
  ext
  · exact h.1
  · exact h.2

lemma exists_pair_of_mem_span {x y z : E3}
    (h_mem : z ∈ Submodule.span ℂ ({x, y} : Set E3)) :
    ∃ p : ℂ × ℂ, z = p.1 • x + p.2 • y := by
  rcases exists_of_mem_span_pair h_mem with ⟨a, b, rfl⟩
  exact ⟨(a, b), rfl⟩

lemma unique_span_coeffs {x y z : E3}
    (h_indep : LinearIndependent ℂ ![x, y])
    (h_mem : z ∈ Submodule.span ℂ ({x, y} : Set E3)) :
    ∃! p : ℂ × ℂ, z = p.1 • x + p.2 • y := by
  rcases exists_pair_of_mem_span h_mem with ⟨p, hp⟩
  refine ⟨p, hp, ?_⟩
  intro q hq
  rw [hp] at hq
  exact prod_unique_of_combos_eq h_indep q p hq.symm

structure SpanCoeffs (A : Matrix (Fin 3) (Fin 3) ℂ) (x : E3) where
  alpha : ℂ
  beta  : ℂ
  h_decomp : (Matrix.toEuclideanLin A).adjoint x = alpha • x + beta • (Matrix.toEuclideanLin A x)

noncomputable def getSpanCoeffs 
    (A : Matrix (Fin 3) (Fin 3) ℂ) 
    (x : E3) 
    (h_indep : LinearIndependent ℂ ![x, (Matrix.toEuclideanLin A) x])
    (h_collapse : (Matrix.toEuclideanLin A).adjoint x ∈ Submodule.span ℂ ({x, (Matrix.toEuclideanLin A) x} : Set E3)) : 
    SpanCoeffs A x :=
  let coeffs := Classical.choose (unique_span_coeffs h_indep h_collapse)
  {
    alpha := coeffs.1
    beta := coeffs.2
    h_decomp := (Classical.choose_spec (unique_span_coeffs h_indep h_collapse)).1
  }

end SpanCoefficients

section InverseCrabb

def HasCrabbProperty (A : Matrix (Fin 3) (Fin 3) ℂ) : Prop :=
  ∃ x : EuclideanSpace ℂ (Fin 3), ‖x‖ = 1 ∧
    ∃ (c : SpanCoeffs A x), ‖c.beta‖ = 1

noncomputable def UpperTri (a b c : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, a, c;
     0, 0, b;
     0, 0, 0]

lemma ic_A01_01_unitary_inv (U : Matrix (Fin 3) (Fin 3) ℂ) (hU : U * U.conjTranspose = 1) :
    U.conjTranspose * U = 1 := by
  rw [mul_eq_one_comm] at hU
  exact hU

lemma ic_A01_02_x_eq_Uy (U : Matrix (Fin 3) (Fin 3) ℂ) (hU : U * U.conjTranspose = 1) (x : E3) :
    let y := Matrix.mulVec U.conjTranspose x
    x = Matrix.mulVec U y := by
  intro y
  simp only [y, Matrix.mulVec_mulVec]
  rw [hU]
  simp

lemma ic_A01_03_01_def (M : Matrix (Fin 3) (Fin 3) ℂ) (v : E3) :
    Matrix.toEuclideanLin M v = Matrix.mulVec M v := rfl
  
lemma ic_A01_03_02_comp (M N : Matrix (Fin 3) (Fin 3) ℂ) (v : E3) :
    Matrix.toEuclideanLin (M * N) v = Matrix.toEuclideanLin M (Matrix.toEuclideanLin N v) := by
  simp only []
  aesop

lemma ic_A01_03_03_inv (U : Matrix (Fin 3) (Fin 3) ℂ) (hU : U * U.conjTranspose = 1) :
    U.conjTranspose * U = 1 := by
  rw [mul_eq_one_comm] at hU
  exact hU

lemma ic_A01_03_04_id (v : E3) :
    Matrix.toEuclideanLin 1 v = v := by
  simp only []
  aesop

lemma ic_A01_03_By_eq (U : Matrix (Fin 3) (Fin 3) ℂ) (A : Matrix (Fin 3) (Fin 3) ℂ)
    (hU : U * U.conjTranspose = 1) (x : E3) :
    let y : E3 := (Matrix.toEuclideanLin U.conjTranspose) x
    let B := U.conjTranspose * A * U
    (Matrix.toEuclideanLin B) y = (Matrix.toEuclideanLin U.conjTranspose) ((Matrix.toEuclideanLin A) x) := by
  intro y B
  rw [ic_A01_03_02_comp (U.conjTranspose * A) U y]
  simp only [y]
  rw [← ic_A01_03_02_comp U U.conjTranspose x]
  rw [hU]
  rw [ic_A01_03_04_id x]
  rw [ic_A01_03_02_comp U.conjTranspose A x]

lemma ic_A01_04_01_B_adj (U A : Matrix (Fin 3) (Fin 3) ℂ) :
    let B := U.conjTranspose * A * U
    B.conjTranspose = U.conjTranspose * A.conjTranspose * U := by
  intro B
  simp only [B, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

lemma ic_adj_01_lhs_expansion (M : Matrix (Fin 3) (Fin 3) ℂ) (x y : E3) :
    ⟪(Matrix.toEuclideanLin M) x, y⟫ = 
    ∑ i : Fin 3, ∑ j : Fin 3, star (M i j * x j) * y i := by
  rw [PiLp.inner_apply]
  simp only [matrix_toEuclideanLin_apply, Matrix.mulVec, dotProduct]
  simp [Finset.sum, Complex.ext_iff]
  ring_nf
  aesop

lemma ic_adj_02_01_term_eq (M : Matrix (Fin 3) (Fin 3) ℂ) (x y : E3) (i j : Fin 3) :
    star (M i j * x j) * y i = star (x j) * (star (M i j) * y i) := by
  rw [StarMul.star_mul (M i j) (x j)]
  rw [mul_assoc]

lemma ic_adj_02_02_rewrite_sums (M : Matrix (Fin 3) (Fin 3) ℂ) (x y : E3) :
    (∑ i : Fin 3, ∑ j : Fin 3, star (M i j * x j) * y i) = 
    (∑ i : Fin 3, ∑ j : Fin 3, star (x j) * (star (M i j) * y i)) := by
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact ic_adj_02_01_term_eq M x y i j

lemma ic_adj_02_03_swap (f : Fin 3 → Fin 3 → ℂ) :
    (∑ i : Fin 3, ∑ j : Fin 3, f i j) = (∑ j : Fin 3, ∑ i : Fin 3, f i j) := by
  exact Finset.sum_comm

lemma ic_adj_02_04_factor (x : E3) (g : Fin 3 → Fin 3 → ℂ) :
    (∑ j : Fin 3, ∑ i : Fin 3, star (x j) * g i j) = 
    (∑ j : Fin 3, star (x j) * ∑ i : Fin 3, g i j) := by
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]

lemma ic_adj_02_swap_sums (M : Matrix (Fin 3) (Fin 3) ℂ) (x y : E3) :
    (∑ i : Fin 3, ∑ j : Fin 3, star (M i j * x j) * y i) = 
    (∑ j : Fin 3, star (x j) * ∑ i : Fin 3, star (M i j) * y i) := by
  rw [ic_adj_02_02_rewrite_sums]
  rw [ic_adj_02_03_swap (fun i j => star (x j) * (star (M i j) * y i))]
  rw [ic_adj_02_04_factor]

  
lemma ic_adj_03_rhs_recognition (M : Matrix (Fin 3) (Fin 3) ℂ) (y : E3) (j : Fin 3) :
    (∑ i : Fin 3, star (M i j) * y i) = ((Matrix.toEuclideanLin M.conjTranspose) y) j := by
  simp only [matrix_toEuclideanLin_apply, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply]

lemma ic_adj_04_inner_eq (M : Matrix (Fin 3) (Fin 3) ℂ) (x y : E3) :
    ⟪(Matrix.toEuclideanLin M) x, y⟫ = ⟪x, (Matrix.toEuclideanLin M.conjTranspose) y⟫ := by
  rw [ic_adj_01_lhs_expansion]
  rw [ic_adj_02_swap_sums]
  show ∑ j : Fin 3, star (x j) * ∑ i : Fin 3, star (M i j) * y i = ⟪x, (Matrix.toEuclideanLin M.conjTranspose) y⟫
  rw [PiLp.inner_apply]
  simp only [matrix_toEuclideanLin_apply, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply]
  simp [Finset.mul_sum, Finset.sum_mul, mul_assoc]
  congr
  funext i
  simp [mul_comm, mul_left_comm]

def ic_adj_cond_def (A B : E3 →L[ℂ] E3) : Prop :=
  ∀ x y : E3, ⟪A x, y⟫ = ⟪x, B y⟫

lemma ic_adj_cond_satisfied (M : Matrix (Fin 3) (Fin 3) ℂ) :
    ic_adj_cond_def 
      (Matrix.toEuclideanLin M).toContinuousLinearMap 
      (Matrix.toEuclideanLin M.conjTranspose).toContinuousLinearMap := by
  intro x y
  simp only []
  exact ic_adj_04_inner_eq M x y

lemma ic_adj_unique_01_zero (v : E3) (h : @inner ℂ E3 _ v v = 0) : v = 0 := by
  exact inner_self_eq_zero.mp h

lemma ic_adj_unique_02_diff (A B : E3 →L[ℂ] E3) (x : E3) 
    (h_norm_sq : @inner ℂ E3 _ (A.adjoint x - B x) (A.adjoint x - B x) = 0) :
    A.adjoint x = B x := by
  have h_diff : A.adjoint x - B x = 0 := ic_adj_unique_01_zero (A.adjoint x - B x) h_norm_sq
  exact eq_of_sub_eq_zero h_diff

lemma ic_adj_unique (A B : E3 →L[ℂ] E3) (h : ic_adj_cond_def A B) :
    A.adjoint = B := by
  apply ContinuousLinearMap.ext
  intro x
  apply ic_adj_unique_02_diff A B x
  let v := A.adjoint x - B x
  change ⟪v, A.adjoint x - B x⟫ = 0
  rw [inner_sub_right]
  rw [ContinuousLinearMap.adjoint_inner_right]
  rw [← h v x]
  exact sub_self _

lemma ic_adj_04_inner_eq_restate (M : Matrix (Fin 3) (Fin 3) ℂ) (x y : E3) :
    ⟪(Matrix.toEuclideanLin M) x, y⟫ = ⟪x, (Matrix.toEuclideanLin M.conjTranspose) y⟫ := by
  exact ic_adj_04_inner_eq M x y

lemma ic_vec_eq_zero_of_inner_self (v : E3) (h : ⟪v, v⟫ = 0) : v = 0 := by
  exact inner_self_eq_zero.mp h

lemma ic_lin_adj_unique (A B : E3 →ₗ[ℂ] E3) 
    (h_prop : ∀ x y, ⟪A x, y⟫ = ⟪x, B y⟫) : 
    A.adjoint = B := by
  apply LinearMap.ext
  intro x
  rw [← sub_eq_zero]
  apply ic_vec_eq_zero_of_inner_self
  let v := A.adjoint x - B x
  change ⟪v, A.adjoint x - B x⟫ = 0
  rw [inner_sub_right]
  rw [LinearMap.adjoint_inner_right]
  rw [h_prop v x]
  exact sub_self _

lemma ic_matrix_maps_satisfy_cond (M : Matrix (Fin 3) (Fin 3) ℂ) :
    ∀ x y, ⟪(Matrix.toEuclideanLin M) x, y⟫ = 
           ⟪x, (Matrix.toEuclideanLin M.conjTranspose) y⟫ := by
  intro x y
  exact ic_adj_04_inner_eq_restate M x y

lemma ic_A01_04_02_clm_adj (M : Matrix (Fin 3) (Fin 3) ℂ) :
    (Matrix.toEuclideanLin M).adjoint = Matrix.toEuclideanLin M.conjTranspose := by
  apply ic_lin_adj_unique
  exact ic_matrix_maps_satisfy_cond M

lemma ic_A01_04_03_mul_apply (M : Matrix (Fin 3) (Fin 3) ℂ) (v : E3) :
    Matrix.toEuclideanLin M v = Matrix.mulVec M v := by
  rfl

lemma ic_cancel_01_combine_vecs (M N : Matrix (Fin 3) (Fin 3) ℂ) (x : E3) :
    M.mulVec (N.mulVec x) = (M * N).mulVec x := by
  rw [Matrix.mulVec_mulVec]

lemma ic_cancel_02_reassoc_matrices (A B C D : Matrix (Fin 3) (Fin 3) ℂ) :
    (A * B * C) * D = A * B * (C * D) := by
  simp only [Matrix.mul_assoc]

lemma ic_cancel_03_apply_unitary (X U : Matrix (Fin 3) (Fin 3) ℂ) (hU : U * U.conjTranspose = 1) :
    X * (U * U.conjTranspose) = X := by
  rw [hU]
  rw [Matrix.mul_one]
  
lemma ic_cancel_04_matrix_identity (U A : Matrix (Fin 3) (Fin 3) ℂ) (hU : U * U.conjTranspose = 1) :
    (U.conjTranspose * A.conjTranspose * U) * U.conjTranspose = U.conjTranspose * A.conjTranspose := by
  rw [ic_cancel_02_reassoc_matrices]
  rw [ic_cancel_03_apply_unitary _ _ hU]

lemma ic_A01_04_04_unitary_cancel (U A : Matrix (Fin 3) (Fin 3) ℂ) (hU : U * U.conjTranspose = 1) (x : E3) :
    (U.conjTranspose * A.conjTranspose * U).mulVec (U.conjTranspose.mulVec x) = 
    U.conjTranspose.mulVec (A.conjTranspose.mulVec x) := by
  rw [ic_cancel_01_combine_vecs]
  rw [ic_cancel_01_combine_vecs]
  rw [ic_cancel_04_matrix_identity U A hU]

lemma ic_Badj_01_simplify_adj (U A : Matrix (Fin 3) (Fin 3) ℂ) :
    let B := U.conjTranspose * A * U
    (Matrix.toEuclideanLin B).adjoint = Matrix.toEuclideanLin (U.conjTranspose * A.conjTranspose * U) := by
  intro B
  rw [ic_A01_04_02_clm_adj B]
  rw [ic_A01_04_01_B_adj U A]

lemma ic_Badj_02_calc_lhs (U A : Matrix (Fin 3) (Fin 3) ℂ) (x : E3) :
    let y : E3 := (Matrix.toEuclideanLin U.conjTranspose) x
    let B_adj_op := Matrix.toEuclideanLin (U.conjTranspose * A.conjTranspose * U)
    B_adj_op y = Matrix.mulVec (U.conjTranspose * A.conjTranspose * U) (Matrix.mulVec U.conjTranspose x) := by
  intro y B_adj_op
  simp only []
  rfl
lemma ic_Badj_03_calc_rhs (U A : Matrix (Fin 3) (Fin 3) ℂ) (x : E3) :
    let A_adj_op := (Matrix.toEuclideanLin A).adjoint
    (Matrix.toEuclideanLin U.conjTranspose) (A_adj_op x) = 
    Matrix.mulVec U.conjTranspose (Matrix.mulVec A.conjTranspose x) := by
  intro A_adj_op
  dsimp only [A_adj_op]
  rw [ic_A01_04_02_clm_adj A]
  simp only [ic_A01_04_03_mul_apply]

lemma ic_Badj_04_vec_eq (U A : Matrix (Fin 3) (Fin 3) ℂ) (hU : U * U.conjTranspose = 1) (x : E3) :
    Matrix.mulVec (U.conjTranspose * A.conjTranspose * U) (Matrix.mulVec U.conjTranspose x) = 
    Matrix.mulVec U.conjTranspose (Matrix.mulVec A.conjTranspose x) := by
  exact ic_A01_04_04_unitary_cancel U A hU x

lemma ic_Badj_04_vec_eq_E3 (U A : Matrix (Fin 3) (Fin 3) ℂ) (hU : U * U.conjTranspose = 1) (x : E3) :
    (Matrix.toEuclideanLin (U.conjTranspose * A.conjTranspose * U)) 
    ((Matrix.toEuclideanLin U.conjTranspose) x) = 
    (Matrix.toEuclideanLin U.conjTranspose) 
    ((Matrix.toEuclideanLin A.conjTranspose) x) := by
  simp only []
  aesop

lemma ic_A01_04_Badj_y_eq (U : Matrix (Fin 3) (Fin 3) ℂ) (A : Matrix (Fin 3) (Fin 3) ℂ)
    (hU : U * U.conjTranspose = 1) (x : E3) :
    let y : E3 := (Matrix.toEuclideanLin U.conjTranspose) x
    let B := U.conjTranspose * A * U
    (Matrix.toEuclideanLin B).adjoint y = (Matrix.toEuclideanLin U.conjTranspose) ((Matrix.toEuclideanLin A).adjoint x) := by
  intro y B
  rw [ic_Badj_01_simplify_adj U A]
  dsimp only [y]
  have h1 : (Matrix.toEuclideanLin (U.conjTranspose * A.conjTranspose * U)) ((Matrix.toEuclideanLin U.conjTranspose) x) = (Matrix.toEuclideanLin U.conjTranspose) ((Matrix.toEuclideanLin A.conjTranspose) x) := by
    apply ic_Badj_04_vec_eq_E3 U A hU x
  rw [h1]
  have h2 : (Matrix.toEuclideanLin A).adjoint x = (Matrix.toEuclideanLin A.conjTranspose) x := by
    rw [ic_A01_04_02_clm_adj A]
  rw [h2]

lemma ic_A01_05_span_map_iso (L : E3 ≃ₗ[ℂ] E3) (u v w : E3) :
    w ∈ Submodule.span ℂ ({u, v} : Set E3) ↔ L w ∈ Submodule.span ℂ ({L u, L v} : Set E3) := by
  constructor
  · intro h
    rw [Submodule.mem_span_pair] at h ⊢
    rcases h with ⟨a, b, rfl⟩
    use a, b
    aesop
  · intro h
    rw [Submodule.mem_span_pair] at h ⊢
    rcases h with ⟨a, b, h_eq⟩
    use a, b
    have : a • u + b • v = L.symm (a • L u + b • L v) := by
      simp [map_add, map_smul]
    rw [this, h_eq]
    simp

noncomputable def ic_span_inv_left_proof (U : Matrix (Fin 3) (Fin 3) ℂ) (hU : U * U.conjTranspose = 1) :
    Matrix.toEuclideanLin U.conjTranspose ∘ₗ Matrix.toEuclideanLin U = LinearMap.id := by
  apply LinearMap.ext
  intro v
  simp only [LinearMap.comp_apply, LinearMap.id_apply]
  rw [← ic_A01_03_02_comp]
  rw [ic_A01_03_03_inv U hU]
  rw [ic_A01_03_04_id]

noncomputable def ic_span_inv_right_proof (U : Matrix (Fin 3) (Fin 3) ℂ) (hU : U * U.conjTranspose = 1) :
    Matrix.toEuclideanLin U ∘ₗ Matrix.toEuclideanLin U.conjTranspose = LinearMap.id := by
  apply LinearMap.ext
  intro v
  simp only [LinearMap.comp_apply, LinearMap.id_apply]
  rw [← ic_A01_03_02_comp]
  rw [hU]
  rw [ic_A01_03_04_id]

noncomputable def ic_span_01_iso_def (U : Matrix (Fin 3) (Fin 3) ℂ) (hU : U * U.conjTranspose = 1) :
    E3 ≃ₗ[ℂ] E3 :=
  LinearEquiv.ofLinear 
    (Matrix.toEuclideanLin U.conjTranspose) 
    (Matrix.toEuclideanLin U) 
    (ic_span_inv_left_proof U hU)
    (ic_span_inv_right_proof U hU)
  
lemma ic_span_02_map_x (U : Matrix (Fin 3) (Fin 3) ℂ) (hU : U * U.conjTranspose = 1) (x : E3) :
    let L := ic_span_01_iso_def U hU
    let y : E3 := (Matrix.toEuclideanLin U.conjTranspose) x
    L x = y := by
  rfl

lemma ic_span_03_map_Ax (U A : Matrix (Fin 3) (Fin 3) ℂ) (hU : U * U.conjTranspose = 1) (x : E3) :
    let L := ic_span_01_iso_def U hU
    let y : E3 := (Matrix.toEuclideanLin U.conjTranspose) x
    let B := U.conjTranspose * A * U
    L ((Matrix.toEuclideanLin A) x) = (Matrix.toEuclideanLin B) y := by
  exact (ic_A01_03_By_eq U A hU x).symm

lemma ic_span_04_map_adj (U A : Matrix (Fin 3) (Fin 3) ℂ) (hU : U * U.conjTranspose = 1) (x : E3) :
    let L := ic_span_01_iso_def U hU
    let y : E3 := (Matrix.toEuclideanLin U.conjTranspose) x
    let B := U.conjTranspose * A * U
    L ((Matrix.toEuclideanLin A).adjoint x) = (Matrix.toEuclideanLin B).adjoint y := by
  exact (ic_A01_04_Badj_y_eq U A hU x).symm

lemma ic_A01_span_transfer (U : Matrix (Fin 3) (Fin 3) ℂ) (A : Matrix (Fin 3) (Fin 3) ℂ)
    (hU : U * U.conjTranspose = 1) (x : E3) :
    let y : E3 := (Matrix.toEuclideanLin U.conjTranspose) x
    let B := U.conjTranspose * A * U
    (Matrix.toEuclideanLin A).adjoint x ∈ Submodule.span ℂ ({x, (Matrix.toEuclideanLin A) x} : Set E3) ↔
    (Matrix.toEuclideanLin B).adjoint y ∈ Submodule.span ℂ ({y, (Matrix.toEuclideanLin B) y} : Set E3) := by
  intro y B
  let L := ic_span_01_iso_def U hU
  have h_iso := ic_A01_05_span_map_iso L 
    x 
    ((Matrix.toEuclideanLin A) x) 
    ((Matrix.toEuclideanLin A).adjoint x)
  rw [ic_span_02_map_x U hU x] at h_iso
  rw [ic_span_03_map_Ax U A hU x] at h_iso
  rw [ic_span_04_map_adj U A hU x] at h_iso
  exact h_iso

lemma ic_indep_d01_iso_exists (U : Matrix (Fin 3) (Fin 3) ℂ) (hU : U * U.conjTranspose = 1) :
    ∃ L : E3 ≃ₗ[ℂ] E3, L.toLinearMap = Matrix.toEuclideanLin U.conjTranspose := by
  use ic_span_01_iso_def U hU
  rfl

lemma ic_indep_d03_vec_fun_ext (f g : Fin 2 → E3) :
    (f 0 = g 0) → (f 1 = g 1) → f = g := by
  intro h0 h1
  ext i
  fin_cases i
  · aesop
  · aesop

lemma ic_indep_d02_01_injective (L : E3 ≃ₗ[ℂ] E3) :
    Function.Injective L.toLinearMap := by
  exact L.injective

lemma ic_indep_d02_02_ker_bot (L : E3 ≃ₗ[ℂ] E3) :
    LinearMap.ker L.toLinearMap = ⊥ := by
  rw [LinearMap.ker_eq_bot]
  exact ic_indep_d02_01_injective L

lemma ic_indep_d02_03_disjoint (L : E3 ≃ₗ[ℂ] E3) (v : Fin 2 → E3) :
    Disjoint (LinearMap.ker L.toLinearMap) (Submodule.span ℂ (Set.range v)) := by
  rw [ic_indep_d02_02_ker_bot L]
  exact disjoint_bot_left

lemma ic_indep_d02_04_forward (L : E3 ≃ₗ[ℂ] E3) (v : Fin 2 → E3) :
    LinearIndependent ℂ v → LinearIndependent ℂ (L ∘ v) := by
  intro h
  change LinearIndependent ℂ (L.toLinearMap ∘ v)
  rw [LinearMap.linearIndependent_iff L.toLinearMap (ic_indep_d02_02_ker_bot L)]
  exact h

lemma ic_indep_d02_iso_preserves_indep_iff (L : E3 ≃ₗ[ℂ] E3) (v : Fin 2 → E3) :
    LinearIndependent ℂ (L ∘ v) ↔ LinearIndependent ℂ v := by
  constructor
  · intro h
    exact LinearIndependent.of_comp L.toLinearMap h
  · intro h
    exact ic_indep_d02_04_forward L v h

lemma ic_indep_d04_matrix_vec_at_0 (u v : E3) :
    ![u, v] 0 = u := by
  simp

lemma ic_indep_d05_matrix_vec_at_1 (u v : E3) :
    ![u, v] 1 = v := by
  simp

lemma ic_indep_d06_comp_apply (L : E3 →ₗ[ℂ] E3) (v : Fin 2 → E3) (i : Fin 2) :
    (L ∘ v) i = L (v i) := rfl

lemma ic_indep_d07_iso_map_pair (L : E3 ≃ₗ[ℂ] E3) (u v : E3) :
    L ∘ ![u, v] = ![L u, L v] := by
  apply ic_indep_d03_vec_fun_ext
  · aesop
  · aesop

lemma ic_indep_d08_L_def (U : Matrix (Fin 3) (Fin 3) ℂ) (hU : U * U.conjTranspose = 1) :
    let L := ic_span_01_iso_def U hU
    L.toLinearMap = (Matrix.toEuclideanLin U.conjTranspose) := by
  rfl

lemma ic_indep_d09_L_x_eq_y (U : Matrix (Fin 3) (Fin 3) ℂ) (hU : U * U.conjTranspose = 1) (x : E3) :
    let L := ic_span_01_iso_def U hU
    let y : E3 := (Matrix.toEuclideanLin U.conjTranspose) x
    L x = y := by
  intro L y
  rfl

lemma ic_indep_d10_L_Ax_eq_By (U A : Matrix (Fin 3) (Fin 3) ℂ) (hU : U * U.conjTranspose = 1) (x : E3) :
    let L := ic_span_01_iso_def U hU
    let y : E3 := (Matrix.toEuclideanLin U.conjTranspose) x
    let B := U.conjTranspose * A * U
    L ((Matrix.toEuclideanLin A) x) = (Matrix.toEuclideanLin B) y := by
  intro L y B
  exact ic_span_03_map_Ax U A hU x

lemma ic_indep_d11_map_vec_0 (U A : Matrix (Fin 3) (Fin 3) ℂ) (hU : U * U.conjTranspose = 1) (x : E3) :
    let L := ic_span_01_iso_def U hU
    let y : E3 := (Matrix.toEuclideanLin U.conjTranspose) x
    ![L x, L ((Matrix.toEuclideanLin A) x)] 0 = y := by
  intro L y
  rw [ic_indep_d04_matrix_vec_at_0]
  exact ic_indep_d09_L_x_eq_y U hU x

lemma ic_indep_d12_map_vec_1 (U A : Matrix (Fin 3) (Fin 3) ℂ) (hU : U * U.conjTranspose = 1) (x : E3) :
    let L := ic_span_01_iso_def U hU
    let y : E3 := (Matrix.toEuclideanLin U.conjTranspose) x
    let B := U.conjTranspose * A * U
    ![L x, L ((Matrix.toEuclideanLin A) x)] 1 = (Matrix.toEuclideanLin B) y := by
  intro L y B
  rw [ic_indep_d05_matrix_vec_at_1]
  exact ic_indep_d10_L_Ax_eq_By U A hU x

lemma ic_indep_d13_family_transform (U A : Matrix (Fin 3) (Fin 3) ℂ) (hU : U * U.conjTranspose = 1) (x : E3) :
    let L := ic_span_01_iso_def U hU
    let y : E3 := (Matrix.toEuclideanLin U.conjTranspose) x
    let B := U.conjTranspose * A * U
    L ∘ ![x, (Matrix.toEuclideanLin A) x] = ![y, (Matrix.toEuclideanLin B) y] := by
  intro L y B
  rw [ic_indep_d07_iso_map_pair]
  apply ic_indep_d03_vec_fun_ext
  · exact ic_indep_d11_map_vec_0 U A hU x
  · exact ic_indep_d12_map_vec_1 U A hU x

lemma ic_A02_indep_transfer (U : Matrix (Fin 3) (Fin 3) ℂ) (A : Matrix (Fin 3) (Fin 3) ℂ)
    (hU : U * U.conjTranspose = 1) (x : E3) :
    let y : E3 := (Matrix.toEuclideanLin U.conjTranspose) x
    let B := U.conjTranspose * A * U
    LinearIndependent ℂ ![x, (Matrix.toEuclideanLin A) x] ↔
    LinearIndependent ℂ ![y, (Matrix.toEuclideanLin B) y] := by
  intro y B
  let L := ic_span_01_iso_def U hU
  have h_equiv := ic_indep_d02_iso_preserves_indep_iff L ![x, (Matrix.toEuclideanLin A) x]
  rw [ic_indep_d13_family_transform U A hU x] at h_equiv
  exact h_equiv.symm

lemma ic_coeffs_d01_mem_image_span (L : E3 ≃ₗ[ℂ] E3) (x z v : E3) 
    (h : v ∈ Submodule.span ℂ ({x, z} : Set E3)) :
    L v ∈ Submodule.span ℂ ({L x, L z} : Set E3) := by
  rw [Submodule.mem_span_pair] at h ⊢
  rcases h with ⟨a, b, rfl⟩
  use a, b
  simp [L.map_add, L.map_smul]

lemma ic_coeffs_d02_apply_combo (L : E3 ≃ₗ[ℂ] E3) (x z : E3) (a b : ℂ) :
    L (a • x + b • z) = a • L x + b • L z := by
  simp [L.map_add, L.map_smul]

lemma ic_coeffs_d03_unique_beta 
    (_x _z : E3) (y w : E3) 
    (_h_indep : LinearIndependent ℂ ![y, w])
    (a b : ℂ)
    (_h_eq : a • y + b • w = a • y + b • w) :
    b = b := rfl

lemma ic_coeffs_d04_01_map_decomp (L : E3 ≃ₗ[ℂ] E3) (x z v : E3) (a b : ℂ)
    (h_decomp : v = a • x + b • z) :
    L v = a • L x + b • L z := by
  rw [h_decomp]
  simp [map_add, map_smul]

lemma ic_coeffs_d04_02_spec_eq (L : E3 ≃ₗ[ℂ] E3) (x z v : E3)
    (h_unique : ∃! p : ℂ × ℂ, L v = p.1 • L x + p.2 • L z) :
    let p := Classical.choose h_unique.exists
    L v = p.1 • L x + p.2 • L z := by
  intro p
  exact Classical.choose_spec h_unique.exists

lemma ic_coeffs_d04_03_pair_eq
    (L : E3 ≃ₗ[ℂ] E3) (x z v : E3)
    (h_indep_img : LinearIndependent ℂ ![L x, L z])
    (h_mem_img : L v ∈ Submodule.span ℂ ({L x, L z} : Set E3))
    (a b : ℂ)
    (h_decomp : v = a • x + b • z) :
    Classical.choose (unique_span_coeffs h_indep_img h_mem_img).exists = (a, b) := by
  have h_unique := unique_span_coeffs h_indep_img h_mem_img
  have h_spec_eq := ic_coeffs_d04_02_spec_eq L x z v h_unique
  have h_my_eq := ic_coeffs_d04_01_map_decomp L x z v a b h_decomp
  apply prod_unique_of_combos_eq h_indep_img
  exact h_spec_eq.symm.trans h_my_eq

lemma ic_coeffs_d04_match_coeffs_general
    (L : E3 ≃ₗ[ℂ] E3) (x z v : E3)
    (h_indep_img : LinearIndependent ℂ ![L x, L z])
    (h_mem_img : L v ∈ Submodule.span ℂ ({L x, L z} : Set E3))
    (a b : ℂ)
    (h_decomp : v = a • x + b • z) :
    let coeffs_img := Classical.choose (unique_span_coeffs h_indep_img h_mem_img).exists
    coeffs_img.2 = b := by
  intro coeffs_img
  have h_pair : Classical.choose (unique_span_coeffs h_indep_img h_mem_img).exists = (a, b) := 
    ic_coeffs_d04_03_pair_eq L x z v h_indep_img h_mem_img a b h_decomp
  dsimp only [coeffs_img]
  rw [h_pair]

lemma ic_coeffs_d05_beta_A_def 
    (A : Matrix (Fin 3) (Fin 3) ℂ) (x : E3)
    (h_indep : LinearIndependent ℂ ![x, (Matrix.toEuclideanLin A) x])
    (h_span : (Matrix.toEuclideanLin A).adjoint x ∈ Submodule.span ℂ ({x, (Matrix.toEuclideanLin A) x} : Set E3)) :
    let c := getSpanCoeffs A x h_indep h_span
    (Matrix.toEuclideanLin A).adjoint x = c.alpha • x + c.beta • ((Matrix.toEuclideanLin A) x) := by
  intro c
  exact c.h_decomp

lemma ic_coeffs_d06_L_def (U : Matrix (Fin 3) (Fin 3) ℂ) (hU : U * U.conjTranspose = 1) :
    let L := ic_span_01_iso_def U hU
    L.toLinearMap = Matrix.toEuclideanLin U.conjTranspose := rfl

lemma ic_coeffs_d07_map_adj (U A : Matrix (Fin 3) (Fin 3) ℂ) (hU : U * U.conjTranspose = 1) (x : E3) :
    let L := ic_span_01_iso_def U hU
    let y := Matrix.toEuclideanLin U.conjTranspose x
    let B := U.conjTranspose * A * U
    L ((Matrix.toEuclideanLin A).adjoint x) = (Matrix.toEuclideanLin B).adjoint y := by
  intro L y B
  exact ic_span_04_map_adj U A hU x

lemma ic_coeffs_d08_map_x (U : Matrix (Fin 3) (Fin 3) ℂ) (hU : U * U.conjTranspose = 1) (x : E3) :
    let L := ic_span_01_iso_def U hU
    let y := Matrix.toEuclideanLin U.conjTranspose x
    L x = y := rfl

lemma ic_coeffs_d09_map_Ax (U A : Matrix (Fin 3) (Fin 3) ℂ) (hU : U * U.conjTranspose = 1) (x : E3) :
    let L := ic_span_01_iso_def U hU
    let y := Matrix.toEuclideanLin U.conjTranspose x
    let B := U.conjTranspose * A * U
    L ((Matrix.toEuclideanLin A) x) = (Matrix.toEuclideanLin B) y := by
  intro L y B
  exact ic_span_03_map_Ax U A hU x

lemma ic_coeffs_d10_transform_eq 
    (U A : Matrix (Fin 3) (Fin 3) ℂ) (hU : U * U.conjTranspose = 1) (x : E3)
    (h_indep : LinearIndependent ℂ ![x, (Matrix.toEuclideanLin A) x])
    (h_span : (Matrix.toEuclideanLin A).adjoint x ∈ Submodule.span ℂ ({x, (Matrix.toEuclideanLin A) x} : Set E3)) :
    let c := getSpanCoeffs A x h_indep h_span
    let _L := ic_span_01_iso_def U hU
    let y := Matrix.toEuclideanLin U.conjTranspose x
    let B := U.conjTranspose * A * U
    (Matrix.toEuclideanLin B).adjoint y = c.alpha • y + c.beta • ((Matrix.toEuclideanLin B) y) := by
  intro c L y B
  have hA := ic_coeffs_d05_beta_A_def A x h_indep h_span
  apply_fun L at hA
  rw [ic_coeffs_d07_map_adj U A hU x] at hA
  rw [map_add, map_smul, map_smul] at hA
  rw [ic_coeffs_d08_map_x U hU x] at hA
  rw [ic_coeffs_d09_map_Ax U A hU x] at hA
  exact hA

lemma ic_coeffs_d11_unique_B 
    (U A : Matrix (Fin 3) (Fin 3) ℂ) (hU : U * U.conjTranspose = 1) (x : E3)
    (h_indep : LinearIndependent ℂ ![x, (Matrix.toEuclideanLin A) x])
    (h_span : (Matrix.toEuclideanLin A).adjoint x ∈ Submodule.span ℂ ({x, (Matrix.toEuclideanLin A) x} : Set E3)) :
    let y := Matrix.toEuclideanLin U.conjTranspose x
    let B := U.conjTranspose * A * U
    let _h_indep_B := (ic_A02_indep_transfer U A hU x).mp h_indep
    let _h_span_B := (ic_A01_span_transfer U A hU x).mp h_span
    ∃! p : ℂ × ℂ, (Matrix.toEuclideanLin B).adjoint y = p.1 • y + p.2 • ((Matrix.toEuclideanLin B) y) := by
  intro y B h_indep_B h_span_B
  exact unique_span_coeffs h_indep_B h_span_B

lemma ic_coeffs_d12_A_coeffs_work_for_B 
    (U A : Matrix (Fin 3) (Fin 3) ℂ) (hU : U * U.conjTranspose = 1) (x : E3)
    (h_indep : LinearIndependent ℂ ![x, (Matrix.toEuclideanLin A) x])
    (h_span : (Matrix.toEuclideanLin A).adjoint x ∈ Submodule.span ℂ ({x, (Matrix.toEuclideanLin A) x} : Set E3)) :
    let c := getSpanCoeffs A x h_indep h_span
    let y := Matrix.toEuclideanLin U.conjTranspose x
    let B := U.conjTranspose * A * U
    (Matrix.toEuclideanLin B).adjoint y = c.alpha • y + c.beta • ((Matrix.toEuclideanLin B) y) := by
  exact ic_coeffs_d10_transform_eq U A hU x h_indep h_span

lemma ic_coeffs_d13_B_coeffs_def
    (U A : Matrix (Fin 3) (Fin 3) ℂ) (hU : U * U.conjTranspose = 1) (x : E3)
    (h_indep : LinearIndependent ℂ ![x, (Matrix.toEuclideanLin A) x])
    (h_span : (Matrix.toEuclideanLin A).adjoint x ∈ Submodule.span ℂ ({x, (Matrix.toEuclideanLin A) x} : Set E3)) :
    let y := Matrix.toEuclideanLin U.conjTranspose x
    let B := U.conjTranspose * A * U
    let h_indep_B := (ic_A02_indep_transfer U A hU x).mp h_indep
    let h_span_B := (ic_A01_span_transfer U A hU x).mp h_span
    let cB := getSpanCoeffs B y h_indep_B h_span_B
    (Matrix.toEuclideanLin B).adjoint y = cB.alpha • y + cB.beta • ((Matrix.toEuclideanLin B) y) := by
  intro y B h_indep_B h_span_B cB
  exact cB.h_decomp

lemma ic_coeffs_d14_equate_combos
    (U A : Matrix (Fin 3) (Fin 3) ℂ) (hU : U * U.conjTranspose = 1) (x : E3)
    (h_indep : LinearIndependent ℂ ![x, (Matrix.toEuclideanLin A) x])
    (h_span : (Matrix.toEuclideanLin A).adjoint x ∈ Submodule.span ℂ ({x, (Matrix.toEuclideanLin A) x} : Set E3)) :
    let cA := getSpanCoeffs A x h_indep h_span
    let y := Matrix.toEuclideanLin U.conjTranspose x
    let B := U.conjTranspose * A * U
    let h_indep_B := (ic_A02_indep_transfer U A hU x).mp h_indep
    let h_span_B := (ic_A01_span_transfer U A hU x).mp h_span
    let cB := getSpanCoeffs B y h_indep_B h_span_B
    cA.alpha • y + cA.beta • ((Matrix.toEuclideanLin B) y) = 
    cB.alpha • y + cB.beta • ((Matrix.toEuclideanLin B) y) := by
  intro cA y B h_indep_B h_span_B cB
  rw [← ic_coeffs_d12_A_coeffs_work_for_B U A hU x h_indep h_span]
  rw [ic_coeffs_d13_B_coeffs_def U A hU x h_indep h_span]

lemma ic_A03_coeffs_match (U : Matrix (Fin 3) (Fin 3) ℂ) (A : Matrix (Fin 3) (Fin 3) ℂ)
    (hU : U * U.conjTranspose = 1) (x : E3) 
    (h_indep : LinearIndependent ℂ ![x, (Matrix.toEuclideanLin A) x])
    (h_span : (Matrix.toEuclideanLin A).adjoint x ∈ Submodule.span ℂ ({x, (Matrix.toEuclideanLin A) x} : Set E3)) :
    let y := Matrix.toEuclideanLin U.conjTranspose x
    let B := U.conjTranspose * A * U
    let h_indep_B := (ic_A02_indep_transfer U A hU x).mp h_indep
    let h_span_B := (ic_A01_span_transfer U A hU x).mp h_span
    (getSpanCoeffs A x h_indep h_span).beta = (getSpanCoeffs B y h_indep_B h_span_B).beta := by
  intro y B h_indep_B h_span_B
  have h_eq := ic_coeffs_d14_equate_combos U A hU x h_indep h_span
  have h_unique := coeffs_unique_of_combos_eq h_indep_B h_eq
  exact h_unique.2

lemma ic_norm_d01_to_lin (U : Matrix (Fin 3) (Fin 3) ℂ) (x : E3) :
    Matrix.mulVec U.conjTranspose x = (Matrix.toEuclideanLin U.conjTranspose) x := by
  rfl

lemma ic_norm_d02_norm_eq_sqrt_inner (v : E3) :
    ‖v‖ = Real.sqrt (Complex.re (@inner ℂ _ _ v v)) := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ)]
  rfl

lemma ic_norm_d03_norm_eq_of_inner_eq (u v : E3) 
    (h : ⟪u, u⟫ = ⟪v, v⟫) : 
    ‖u‖ = ‖v‖ := by
  rw [ic_norm_d02_norm_eq_sqrt_inner u]
  rw [ic_norm_d02_norm_eq_sqrt_inner v]
  rw [h]

lemma ic_norm_d04_lhs_inner (U : Matrix (Fin 3) (Fin 3) ℂ) (x : E3) :
    let y := (Matrix.toEuclideanLin U.conjTranspose) x
    ⟪y, y⟫ = ⟪(Matrix.toEuclideanLin U.conjTranspose) x, (Matrix.toEuclideanLin U.conjTranspose) x⟫ := by
  rfl

lemma ic_norm_d05_adjoint_shift (U : Matrix (Fin 3) (Fin 3) ℂ) (x : E3) :
    let y := (Matrix.toEuclideanLin U.conjTranspose) x
    ⟪y, y⟫ = ⟪x, (Matrix.toEuclideanLin U.conjTranspose.conjTranspose) y⟫ := by
  intro y
  rw [ic_adj_04_inner_eq U.conjTranspose x y]

lemma ic_norm_d06_conj_conj (U : Matrix (Fin 3) (Fin 3) ℂ) :
    U.conjTranspose.conjTranspose = U := by
  exact Matrix.conjTranspose_conjTranspose U

lemma ic_norm_d07_inner_simplified (U : Matrix (Fin 3) (Fin 3) ℂ) (x : E3) :
    let y := (Matrix.toEuclideanLin U.conjTranspose) x
    ⟪x, (Matrix.toEuclideanLin U.conjTranspose.conjTranspose) y⟫ = 
    ⟪x, (Matrix.toEuclideanLin U) y⟫ := by
  intro y
  rw [ic_norm_d06_conj_conj]

lemma ic_norm_d08_expand_y (U : Matrix (Fin 3) (Fin 3) ℂ) (x : E3) :
    let y := (Matrix.toEuclideanLin U.conjTranspose) x
    ⟪x, (Matrix.toEuclideanLin U) y⟫ = 
    ⟪x, (Matrix.toEuclideanLin U) ((Matrix.toEuclideanLin U.conjTranspose) x)⟫ := by
  rfl

lemma ic_norm_d09_compose_matrices (U : Matrix (Fin 3) (Fin 3) ℂ) (x : E3) :
    (Matrix.toEuclideanLin U) ((Matrix.toEuclideanLin U.conjTranspose) x) = 
    (Matrix.toEuclideanLin (U * U.conjTranspose)) x := by
  rw [ic_A01_03_02_comp]

lemma ic_norm_d10_apply_unitary (U : Matrix (Fin 3) (Fin 3) ℂ) (hU : U * U.conjTranspose = 1) :
    U * U.conjTranspose = 1 := by
  exact hU

lemma ic_norm_d11_sub_identity (U : Matrix (Fin 3) (Fin 3) ℂ) (hU : U * U.conjTranspose = 1) (x : E3) :
    (Matrix.toEuclideanLin (U * U.conjTranspose)) x = (Matrix.toEuclideanLin 1) x := by
  rw [ic_norm_d10_apply_unitary U hU]

lemma ic_norm_d12_identity_action (x : E3) :
    (Matrix.toEuclideanLin 1) x = x := by
  exact ic_A01_03_04_id x

lemma ic_norm_d13_inner_preserved (U : Matrix (Fin 3) (Fin 3) ℂ) (hU : U * U.conjTranspose = 1) (x : E3) :
    let y := (Matrix.toEuclideanLin U.conjTranspose) x
    ⟪y, y⟫ = ⟪x, x⟫ := by
  intro y
  rw [ic_norm_d05_adjoint_shift U x]
  rw [ic_norm_d07_inner_simplified U x]
  rw [ic_norm_d08_expand_y U x]
  rw [ic_norm_d09_compose_matrices U x]
  rw [ic_norm_d11_sub_identity U hU x]
  rw [ic_norm_d12_identity_action x]

lemma ic_norm_step1_unfold_app (U : Matrix (Fin 3) (Fin 3) ℂ) (x : E3) :
    (Matrix.toEuclideanLin U.conjTranspose) x = WithLp.toLp (p := 2) (Matrix.mulVec U.conjTranspose x) := by
  rw [matrix_toEuclideanLin_apply_toLp]

lemma ic_norm_step2_norm_congr (U : Matrix (Fin 3) (Fin 3) ℂ) (x : E3) :
    ‖(Matrix.toEuclideanLin U.conjTranspose) x‖ = ‖WithLp.toLp (p := 2) (Matrix.mulVec U.conjTranspose x)‖ := by
  rw [ic_norm_step1_unfold_app]

lemma ic_norm_s01_norm_eq_of_inner (u v : E3) (h : @inner ℂ _ _ u u = @inner ℂ _ _ v v) :
    ‖u‖ = ‖v‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ) u]
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ) v]
  rw [h]

lemma ic_norm_s02_inner_preserved (U : Matrix (Fin 3) (Fin 3) ℂ) (hU : U * U.conjTranspose = 1) (x : E3) :
    @inner ℂ _ _ ((Matrix.toEuclideanLin U.conjTranspose) x) ((Matrix.toEuclideanLin U.conjTranspose) x) = 
    @inner ℂ _ _ x x := by
  exact ic_norm_d13_inner_preserved U hU x

lemma ic_norm_s03_lin_norm_preservation (U : Matrix (Fin 3) (Fin 3) ℂ) (hU : U * U.conjTranspose = 1) (x : E3) :
    ‖(Matrix.toEuclideanLin U.conjTranspose) x‖ = ‖x‖ := by
  apply ic_norm_s01_norm_eq_of_inner
  exact ic_norm_s02_inner_preserved U hU x

lemma ic_A04_norm_preservation (U : Matrix (Fin 3) (Fin 3) ℂ) (hU : U * U.conjTranspose = 1) (x : E3) :
    ‖(Matrix.toEuclideanLin U.conjTranspose) x‖ = ‖x‖ := by
  exact ic_norm_s03_lin_norm_preservation U hU x

lemma ic_inv_d01_inv_unitary (U : Matrix (Fin 3) (Fin 3) ℂ) (hU : U * U.conjTranspose = 1) :
    U.conjTranspose * U = 1 := by
  rw [mul_eq_one_comm] at hU
  exact hU

lemma ic_inv_s01_align_right (U A : Matrix (Fin 3) (Fin 3) ℂ) :
    let B := U.conjTranspose * A * U
    U * B * U.conjTranspose = U * (U.conjTranspose * A * (U * U.conjTranspose)) := by
  intro B
  simp only [B]
  simp only [Matrix.mul_assoc]

lemma ic_inv_s02_cancel_right (U A : Matrix (Fin 3) (Fin 3) ℂ) (hU : U * U.conjTranspose = 1) :
    U * (U.conjTranspose * A * (U * U.conjTranspose)) = U * (U.conjTranspose * A) := by
  rw [hU]
  rw [Matrix.mul_one]

lemma ic_inv_s03_assoc_left (U A : Matrix (Fin 3) (Fin 3) ℂ) :
    U * (U.conjTranspose * A) = (U * U.conjTranspose) * A := by
  rw [← Matrix.mul_assoc]

lemma ic_inv_s04_cancel_left (U A : Matrix (Fin 3) (Fin 3) ℂ) (hU : U * U.conjTranspose = 1) :
    (U * U.conjTranspose) * A = A := by
  rw [hU]
  rw [Matrix.one_mul]

lemma ic_inv_d02_A_from_B (U : Matrix (Fin 3) (Fin 3) ℂ) (A : Matrix (Fin 3) (Fin 3) ℂ) 
    (hU : U * U.conjTranspose = 1) :
    let B := U.conjTranspose * A * U
    A = U * B * U.conjTranspose := by
  intro B
  symm
  rw [ic_inv_s01_align_right]
  rw [ic_inv_s02_cancel_right U A hU]
  rw [ic_inv_s03_assoc_left]
  rw [ic_inv_s04_cancel_left U A hU]

lemma ic_norm_U_s01_adjoint_is_unitary (U : Matrix (Fin 3) (Fin 3) ℂ) (hU : U * U.conjTranspose = 1) :
    let V := U.conjTranspose
    V * V.conjTranspose = 1 := by
  intro V
  simp only [V]
  rw [Matrix.conjTranspose_conjTranspose]
  exact ic_inv_d01_inv_unitary U hU

lemma ic_norm_U_s02_apply_preservation (U : Matrix (Fin 3) (Fin 3) ℂ) (hU : U * U.conjTranspose = 1) (y : E3) :
    let V := U.conjTranspose
    ‖(Matrix.toEuclideanLin V.conjTranspose) y‖ = ‖y‖ := by
  intro V
  have hV_unitary : V * V.conjTranspose = 1 := ic_norm_U_s01_adjoint_is_unitary U hU
  exact ic_A04_norm_preservation V hV_unitary y

lemma ic_norm_U_s03_simplify_adj (U : Matrix (Fin 3) (Fin 3) ℂ) :
    U.conjTranspose.conjTranspose = U := by
  exact Matrix.conjTranspose_conjTranspose U

lemma ic_norm_U_s04_rewrite_goal (U : Matrix (Fin 3) (Fin 3) ℂ) (y : E3) :
    ‖(Matrix.toEuclideanLin U.conjTranspose.conjTranspose) y‖ = ‖(Matrix.toEuclideanLin U) y‖ := by
  rw [ic_norm_U_s03_simplify_adj]


lemma ic_inv_d03_norm_U_y (U : Matrix (Fin 3) (Fin 3) ℂ) (hU : U * U.conjTranspose = 1) (y : E3) :
    ‖(Matrix.toEuclideanLin U) y‖ = ‖y‖ := by
  let V := U.conjTranspose
  have h_result := ic_norm_U_s02_apply_preservation U hU y
  dsimp only [V] at h_result
  rw [ic_norm_U_s04_rewrite_goal] at h_result
  exact h_result

lemma ic_inv_d04_unit_map (U : Matrix (Fin 3) (Fin 3) ℂ) (hU : U * U.conjTranspose = 1) (y : E3) 
    (hy : ‖y‖ = 1) :
    ‖(Matrix.toEuclideanLin U) y‖ = 1 := by
  rw [ic_inv_d03_norm_U_y U hU y]
  exact hy

lemma ic_inv_s05_cancellation (U : Matrix (Fin 3) (Fin 3) ℂ) (hU : U * U.conjTranspose = 1) (y : E3) :
    (Matrix.toEuclideanLin U.conjTranspose) ((Matrix.toEuclideanLin U) y) = y := by
  rw [← ic_A01_03_02_comp]
  rw [ic_inv_d01_inv_unitary U hU]
  rw [ic_A01_03_04_id]

lemma ic_inv_s05_lhs_step1 
    (U A : Matrix (Fin 3) (Fin 3) ℂ) (hU : U * U.conjTranspose = 1) (y : E3) :
    let L := ic_span_01_iso_def U hU
    let B := U.conjTranspose * A * U
    L ((Matrix.toEuclideanLin A).adjoint ((Matrix.toEuclideanLin U) y)) = 
    (Matrix.toEuclideanLin B).adjoint (L ((Matrix.toEuclideanLin U) y)) := by
  intro L B
  rw [ic_span_04_map_adj U A hU ((Matrix.toEuclideanLin U) y)]
  aesop

lemma ic_inv_s05_lhs_step2 (U : Matrix (Fin 3) (Fin 3) ℂ) (hU : U * U.conjTranspose = 1) (v : E3) :
    let L := ic_span_01_iso_def U hU
    L v = (Matrix.toEuclideanLin U.conjTranspose) v := by
  rfl

lemma ic_inv_s05_lhs_step3 (U : Matrix (Fin 3) (Fin 3) ℂ) (hU : U * U.conjTranspose = 1) (y : E3) :
    let L := ic_span_01_iso_def U hU
    L ((Matrix.toEuclideanLin U) y) = (Matrix.toEuclideanLin U.conjTranspose) ((Matrix.toEuclideanLin U) y) := by
  intro L
  rw [ic_inv_s05_lhs_step2 U hU]

lemma ic_inv_s05_lhs_step4 (U : Matrix (Fin 3) (Fin 3) ℂ) (hU : U * U.conjTranspose = 1) (y : E3) :
    (Matrix.toEuclideanLin U.conjTranspose) ((Matrix.toEuclideanLin U) y) = y := by
  exact ic_inv_s05_cancellation U hU y

lemma ic_inv_s05_lhs_simp 
    (U A : Matrix (Fin 3) (Fin 3) ℂ) (hU : U * U.conjTranspose = 1) (y : E3) :
    let L := ic_span_01_iso_def U hU
    let B := U.conjTranspose * A * U
    L ((Matrix.toEuclideanLin A).adjoint ((Matrix.toEuclideanLin U) y)) = (Matrix.toEuclideanLin B).adjoint y := by
  intro L B
  rw [ic_inv_s05_lhs_step1 U A hU y]
  rw [ic_inv_s05_lhs_step3 U hU y]
  rw [ic_inv_s05_lhs_step4 U hU y]

lemma ic_inv_s05_rhs_term1 
    (U : Matrix (Fin 3) (Fin 3) ℂ) (hU : U * U.conjTranspose = 1) (y : E3) (alpha : ℂ) :
    let L := ic_span_01_iso_def U hU
    L (alpha • (Matrix.toEuclideanLin U) y) = alpha • y := by
  intro L
  rw [map_smul]
  rw [ic_span_02_map_x U hU ((Matrix.toEuclideanLin U) y)]
  rw [ic_inv_s05_cancellation U hU y]

lemma ic_inv_rhs2_s01_linearity 
    (U : Matrix (Fin 3) (Fin 3) ℂ) (hU : U * U.conjTranspose = 1) (beta : ℂ) (v : E3) :
    let L := ic_span_01_iso_def U hU
    L (beta • v) = beta • L v := by
  intro L
  rw [map_smul]

lemma ic_inv_rhs2_s02_map_A 
    (U A : Matrix (Fin 3) (Fin 3) ℂ) (hU : U * U.conjTranspose = 1) (y : E3) :
    let L := ic_span_01_iso_def U hU
    let B := U.conjTranspose * A * U
    L ((Matrix.toEuclideanLin A) ((Matrix.toEuclideanLin U) y)) = 
    (Matrix.toEuclideanLin B) (L ((Matrix.toEuclideanLin U) y)) := by
  intro L B
  rw [ic_span_03_map_Ax U A hU ((Matrix.toEuclideanLin U) y)]
  aesop

lemma ic_inv_rhs2_s03_expand_L 
    (U : Matrix (Fin 3) (Fin 3) ℂ) (hU : U * U.conjTranspose = 1) (y : E3) :
    let L := ic_span_01_iso_def U hU
    L ((Matrix.toEuclideanLin U) y) = (Matrix.toEuclideanLin U.conjTranspose) ((Matrix.toEuclideanLin U) y) := by
  intro L
  rw [ic_span_02_map_x U hU ((Matrix.toEuclideanLin U) y)]

lemma ic_inv_rhs2_s04_cancel 
    (U : Matrix (Fin 3) (Fin 3) ℂ) (hU : U * U.conjTranspose = 1) (y : E3) :
    (Matrix.toEuclideanLin U.conjTranspose) ((Matrix.toEuclideanLin U) y) = y := by
  exact ic_inv_s05_cancellation U hU y

lemma ic_inv_s05_rhs_term2
    (U A : Matrix (Fin 3) (Fin 3) ℂ) (hU : U * U.conjTranspose = 1) (y : E3) (beta : ℂ) :
    let L := ic_span_01_iso_def U hU
    let B := U.conjTranspose * A * U
    L (beta • (Matrix.toEuclideanLin A) ((Matrix.toEuclideanLin U) y)) = beta • (Matrix.toEuclideanLin B) y := by
  intro L B
  rw [ic_inv_rhs2_s01_linearity U hU beta]
  rw [ic_inv_rhs2_s02_map_A U A hU y]
  rw [ic_inv_rhs2_s03_expand_L U hU y]
  rw [ic_inv_rhs2_s04_cancel U hU y]

lemma ic_inv_d05_decomp_transform 
    (U A : Matrix (Fin 3) (Fin 3) ℂ) (hU : U * U.conjTranspose = 1) 
    (y : E3) (alpha beta : ℂ)
    (h_decomp_A : (Matrix.toEuclideanLin A).adjoint ((Matrix.toEuclideanLin U) y) = 
                  alpha • ((Matrix.toEuclideanLin U) y) + beta • ((Matrix.toEuclideanLin A) ((Matrix.toEuclideanLin U) y))) :
    let B := U.conjTranspose * A * U
    (Matrix.toEuclideanLin B).adjoint y = alpha • y + beta • ((Matrix.toEuclideanLin B) y) := by
  intro B
  let L := ic_span_01_iso_def U hU
  apply_fun L at h_decomp_A
  rw [ic_inv_s05_lhs_simp U A hU y] at h_decomp_A
  rw [map_add] at h_decomp_A
  rw [ic_inv_s05_rhs_term1 U hU y alpha] at h_decomp_A
  rw [ic_inv_s05_rhs_term2 U A hU y beta] at h_decomp_A
  exact h_decomp_A

lemma ic_inv_construct_s01_get_decomp
    (U A : Matrix (Fin 3) (Fin 3) ℂ) (y : E3) 
    (cA : SpanCoeffs A ((Matrix.toEuclideanLin U) y)) :
    (Matrix.toEuclideanLin A).adjoint ((Matrix.toEuclideanLin U) y) = 
    cA.alpha • ((Matrix.toEuclideanLin U) y) + cA.beta • ((Matrix.toEuclideanLin A) ((Matrix.toEuclideanLin U) y)) := by
  exact cA.h_decomp

lemma ic_inv_construct_s02_transform_decomp
    (U A : Matrix (Fin 3) (Fin 3) ℂ) (hU : U * U.conjTranspose = 1) 
    (y : E3) 
    (cA : SpanCoeffs A ((Matrix.toEuclideanLin U) y)) :
    let B := U.conjTranspose * A * U
    (Matrix.toEuclideanLin B).adjoint y = cA.alpha • y + cA.beta • ((Matrix.toEuclideanLin B) y) := by
  intro B
  have h_decomp_A := ic_inv_construct_s01_get_decomp U A y cA
  exact ic_inv_d05_decomp_transform U A hU y cA.alpha cA.beta h_decomp_A

def ic_inv_construct_s03_def_alpha 
    (U A : Matrix (Fin 3) (Fin 3) ℂ) (y : E3) 
    (cA : SpanCoeffs A ((Matrix.toEuclideanLin U) y)) : 
    ℂ := cA.alpha

def ic_inv_construct_s04_def_beta 
    (U A : Matrix (Fin 3) (Fin 3) ℂ) (y : E3) 
    (cA : SpanCoeffs A ((Matrix.toEuclideanLin U) y)) : 
    ℂ := cA.beta

noncomputable def ic_inv_d06_construct_B_coeffs 
    (U A : Matrix (Fin 3) (Fin 3) ℂ) (hU : U * U.conjTranspose = 1) 
    (y : E3) 
    (cA : SpanCoeffs A ((Matrix.toEuclideanLin U) y)) :
    let B := U.conjTranspose * A * U
    SpanCoeffs B y := 
  let _h_nonemptyB := U.conjTranspose * A * U
  {
    alpha := ic_inv_construct_s03_def_alpha U A y cA
    beta  := ic_inv_construct_s04_def_beta U A y cA
    h_decomp := ic_inv_construct_s02_transform_decomp U A hU y cA
  }

lemma ic_inv_d07_forward (U A : Matrix (Fin 3) (Fin 3) ℂ) (hU : U * U.conjTranspose = 1) :
    HasCrabbProperty A → HasCrabbProperty (U.conjTranspose * A * U) := by
  intro hA
  rcases hA with ⟨x, hx_unit, cA, h_beta_norm⟩
  let B := U.conjTranspose * A * U
  let y := (Matrix.toEuclideanLin U.conjTranspose) x
  have hy_unit : ‖y‖ = 1 := by
    have h_unitary : U.conjTranspose * U.conjTranspose.conjTranspose = 1 := by
      rw [Matrix.conjTranspose_conjTranspose]
      rw [mul_eq_one_comm] at hU
      exact hU
    exact ic_inv_d04_unit_map U.conjTranspose h_unitary x hx_unit
  have h_x_eq_Uy : x = (Matrix.toEuclideanLin U) y := by
    simp [y, Matrix.toEuclideanLin]
    aesop
  refine ⟨y, hy_unit, ?_⟩
  let cB := ic_inv_d06_construct_B_coeffs U A hU y (h_x_eq_Uy ▸ cA)
  use cB
  have h_type_eq : SpanCoeffs A ((toEuclideanLin U) y) = SpanCoeffs A x := by
    rw [h_x_eq_Uy]
  show ‖cB.beta‖ = 1
  have h_eq : cB.beta = cA.beta := by
    have h1 : cB.beta = (h_x_eq_Uy ▸ cA).beta := by 
      dsimp [ic_inv_d06_construct_B_coeffs, ic_inv_construct_s04_def_beta]
      rfl
    rw [h1]
    have h_triv : ∀ {x y : E3} (h : x = y) (s : SpanCoeffs A x),
      (h ▸ s : SpanCoeffs A y).beta = s.beta := by
      intro x y h s
      cases h
      rfl
    exact h_triv h_x_eq_Uy cA
  rw [h_eq]
  exact h_beta_norm

lemma ic_inv_d08_adj_unitary (U : Matrix (Fin 3) (Fin 3) ℂ) (hU : U * U.conjTranspose = 1) :
    let V := U.conjTranspose
    V * V.conjTranspose = 1 := by
  intro V
  simp only [V, Matrix.conjTranspose_conjTranspose]
  rw [mul_eq_one_comm] at hU
  exact hU

lemma ic_subst_s01_group_terms (U A : Matrix (Fin 3) (Fin 3) ℂ) :
    let V := U.conjTranspose
    let B := U.conjTranspose * A * U
    V.conjTranspose * B * V = (U * U.conjTranspose) * A * (U * U.conjTranspose) := by
  intro V B
  simp only [V, B, Matrix.conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]

lemma ic_subst_s02_unitary_id (U : Matrix (Fin 3) (Fin 3) ℂ) (hU : U * U.conjTranspose = 1) :
    U * U.conjTranspose = 1 := by
  exact hU

lemma ic_subst_s03_subst_left (U A : Matrix (Fin 3) (Fin 3) ℂ) (hU : U * U.conjTranspose = 1) :
    (U * U.conjTranspose) * A * (U * U.conjTranspose) = 1 * A * (U * U.conjTranspose) := by
  rw [ic_subst_s02_unitary_id U hU]

lemma ic_subst_s04_simplify_identity (U A : Matrix (Fin 3) (Fin 3) ℂ) (hU : U * U.conjTranspose = 1) :
    1 * A * (U * U.conjTranspose) = A := by
  rw [ic_subst_s02_unitary_id U hU]
  simp

lemma ic_inv_d09_subst_check 
    (U A : Matrix (Fin 3) (Fin 3) ℂ) (hU : U * U.conjTranspose = 1) :
    let V := U.conjTranspose
    let B := U.conjTranspose * A * U
    V.conjTranspose * B * V = A := by
  intro V B
  rw [ic_subst_s01_group_terms U A]
  rw [ic_subst_s03_subst_left U A hU]
  rw [ic_subst_s04_simplify_identity U A hU]

lemma ic_back_s01_define_V (U : Matrix (Fin 3) (Fin 3) ℂ) :
    let V := U.conjTranspose
    V = U.conjTranspose := rfl
  
lemma ic_back_s02_V_unitary (U : Matrix (Fin 3) (Fin 3) ℂ) (hU : U * U.conjTranspose = 1) :
    let V := U.conjTranspose
    V * V.conjTranspose = 1 := by
  intro V
  simp only [V, Matrix.conjTranspose_conjTranspose]
  rw [mul_eq_one_comm] at hU
  exact hU

lemma ic_back_s03_apply_forward 
    (U A : Matrix (Fin 3) (Fin 3) ℂ) (hU : U * U.conjTranspose = 1) 
    (hB : HasCrabbProperty (U.conjTranspose * A * U)) :
    let V := U.conjTranspose
    let B := U.conjTranspose * A * U
    HasCrabbProperty (V.conjTranspose * B * V) := by
  intro V B
  have hV_uni := ic_back_s02_V_unitary U hU
  apply ic_inv_d07_forward V B hV_uni
  exact hB

lemma ic_back_s04_simplify_to_A 
    (U A : Matrix (Fin 3) (Fin 3) ℂ) (hU : U * U.conjTranspose = 1) :
    let V := U.conjTranspose
    let B := U.conjTranspose * A * U
    V.conjTranspose * B * V = A := by
  exact ic_inv_d09_subst_check U A hU

lemma ic_inv_d10_backward (U A : Matrix (Fin 3) (Fin 3) ℂ) (hU : U * U.conjTranspose = 1) :
    HasCrabbProperty (U.conjTranspose * A * U) → HasCrabbProperty A := by
  intro hB
  let V := U.conjTranspose
  let B := U.conjTranspose * A * U
  have h_transform := ic_back_s03_apply_forward U A hU hB
  have h_eq := ic_back_s04_simplify_to_A U A hU
  dsimp only [V, B] at h_transform h_eq
  rw [h_eq] at h_transform
  exact h_transform

lemma ic_A_unitary_invariance (U : Matrix (Fin 3) (Fin 3) ℂ) (A : Matrix (Fin 3) (Fin 3) ℂ)
    (hU : U * U.conjTranspose = 1) :
    HasCrabbProperty A ↔ HasCrabbProperty (U.conjTranspose * A * U) := by
  constructor
  · exact ic_inv_d07_forward U A hU
  · exact ic_inv_d10_backward U A hU

lemma ic_nil_s01_matrix_poly_zero (A : Matrix (Fin 3) (Fin 3) ℂ) (h : A ^ 3 = 0) :
    Polynomial.aeval A ((Polynomial.X : Polynomial ℂ) ^ 3) = 0 := by
  rw [Polynomial.aeval_X_pow]
  exact h

lemma ic_nil_s02_map_pow_zero (A : Matrix (Fin 3) (Fin 3) ℂ) (h : A ^ 3 = 0) :
    (Matrix.toLin' A) ^ 3 = 0 := by
  rw [← Matrix.toLin'_pow]
  rw [h]
  exact map_zero (Matrix.toLin')

lemma ic_nil_s01_map_pow_zero (A : Matrix (Fin 3) (Fin 3) ℂ) (h : A ^ 3 = 0) :
    (Matrix.toLin' A) ^ 3 = 0 := by
  rw [← Matrix.toLin'_pow]
  rw [h]
  exact map_zero (Matrix.toLin')

lemma ic_eig_s01_pow_simp (A : Matrix (Fin 3) (Fin 3) ℂ) (mu : ℂ) (v : Fin 3 → ℂ) :
    let T : Module.End ℂ (Fin 3 → ℂ) := Matrix.toLin' A - mu • 1
    (T ^ 1) v = T v := by
  intro T
  simp only [pow_one]

lemma ic_eig_s02_map_simp (A : Matrix (Fin 3) (Fin 3) ℂ) (mu : ℂ) (v : Fin 3 → ℂ) :
    (Matrix.toLin' A - mu • 1) v = (Matrix.toLin' A) v - mu • v := by
  rw [LinearMap.sub_apply]
  aesop

lemma ic_eig_s03_kernel_to_eq (A : Matrix (Fin 3) (Fin 3) ℂ) (mu : ℂ) (v : Fin 3 → ℂ) 
    (h : (Matrix.toLin' A - mu • 1) v = 0) :
    (Matrix.toLin' A) v = mu • v := by
  rw [ic_eig_s02_map_simp] at h
  rwa [sub_eq_zero] at h

lemma ic_eig_s04_exists_v (A : Matrix (Fin 3) (Fin 3) ℂ) (mu : ℂ)
    (h_mu : Module.End.HasEigenvalue (Matrix.toLin' A) mu) :
    ∃ v : Fin 3 → ℂ, v ≠ 0 ∧ (Matrix.toLin' A - mu • 1) v = 0 := by
  have h_ne_bot : Module.End.eigenspace (Matrix.toLin' A) mu ≠ ⊥ := h_mu
  rcases Submodule.exists_mem_ne_zero_of_ne_bot h_ne_bot with ⟨v, hv_mem, hv_ne⟩
  use v, hv_ne
  rw [Module.End.mem_eigenspace_iff] at hv_mem
  rw [ic_eig_s02_map_simp]
  rw [sub_eq_zero]
  exact hv_mem

lemma ic_nil_pow_s01_get_eigenvector (A : Matrix (Fin 3) (Fin 3) ℂ) (mu : ℂ)
    (h_mu : Module.End.HasEigenvalue (Matrix.toLin' A) mu) :
    ∃ v : (Fin 3 → ℂ), v ≠ 0 ∧ (Matrix.toLin' A) v = mu • v := by
  rcases ic_eig_s04_exists_v A mu h_mu with ⟨v, hv_ne, hv_ker⟩
  use v, hv_ne
  exact ic_eig_s03_kernel_to_eq A mu v hv_ker

lemma ic_nil_pow_s02_apply_once (A : Matrix (Fin 3) (Fin 3) ℂ) (mu : ℂ)
    (v : Fin 3 → ℂ) (h_eq : (Matrix.toLin' A) v = mu • v) :
    (Matrix.toLin' A) v = mu • v := by
  exact h_eq

lemma ic_pow2_s01_subst_inner (A : Matrix (Fin 3) (Fin 3) ℂ) (mu : ℂ)
    (v : Fin 3 → ℂ) (h_eq : (Matrix.toLin' A) v = mu • v) :
    (Matrix.toLin' A) ((Matrix.toLin' A) v) = (Matrix.toLin' A) (mu • v) := by
  rw [h_eq]

lemma ic_pow2_s02_linearity (A : Matrix (Fin 3) (Fin 3) ℂ) (mu : ℂ)
    (v : Fin 3 → ℂ) :
    (Matrix.toLin' A) (mu • v) = mu • ((Matrix.toLin' A) v) := by
  rw [LinearMap.map_smul]

lemma ic_pow2_s03_subst_outer (A : Matrix (Fin 3) (Fin 3) ℂ) (mu : ℂ)
    (v : Fin 3 → ℂ) (h_eq : (Matrix.toLin' A) v = mu • v) :
    mu • ((Matrix.toLin' A) v) = mu • (mu • v) := by
  rw [h_eq]

lemma ic_pow2_s04_smul_assoc (mu : ℂ) (v : Fin 3 → ℂ) :
    mu • (mu • v) = (mu * mu) • v := by
  rw [smul_smul]

lemma ic_pow2_s05_scalar_sq (mu : ℂ) :
    mu * mu = mu ^ 2 := by
  ring

lemma ic_nil_pow_s03_apply_twice (A : Matrix (Fin 3) (Fin 3) ℂ) (mu : ℂ)
    (v : Fin 3 → ℂ) (h_eq : (Matrix.toLin' A) v = mu • v) :
    (Matrix.toLin' A) ((Matrix.toLin' A) v) = (mu ^ 2) • v := by
  rw [ic_pow2_s01_subst_inner A mu v h_eq]
  rw [ic_pow2_s02_linearity A mu v]
  rw [ic_pow2_s03_subst_outer A mu v h_eq]
  rw [ic_pow2_s04_smul_assoc]
  rw [ic_pow2_s05_scalar_sq]

lemma ic_zero_s01_ne_bot (mu : ℂ)
    (h_eig : Module.End.HasEigenvalue (0 : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ)) mu) :
    Module.End.eigenspace (0 : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ)) mu ≠ ⊥ := by
  exact h_eig

lemma ic_zero_s02_exists_v (mu : ℂ)
    (h_ne_bot : Module.End.eigenspace (0 : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ)) mu ≠ ⊥) :
    ∃ v : Fin 3 → ℂ, v ≠ 0 ∧ v ∈ Module.End.eigenspace (0 : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ)) mu := by
  rcases Submodule.exists_mem_ne_zero_of_ne_bot h_ne_bot with ⟨v, hv_mem, hv_ne⟩
  use v

lemma ic_zero_s03_mem_iff (mu : ℂ) (v : Fin 3 → ℂ) 
    (h_mem : v ∈ Module.End.eigenspace (0 : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ)) mu) :
    (0 : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ)) v = mu • v := by
  rw [Module.End.mem_eigenspace_iff] at h_mem
  exact h_mem

lemma ic_zero_s04_apply_zero (mu : ℂ) (v : Fin 3 → ℂ)
    (h_eq : (0 : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ)) v = mu • v) :
    0 = mu • v := by
  rw [LinearMap.zero_apply] at h_eq
  exact h_eq

lemma ic_zero_s05_solve (mu : ℂ) (v : Fin 3 → ℂ) (hv_ne : v ≠ 0) (h_eq : 0 = mu • v) :
    mu = 0 := by
  symm at h_eq
  rw [smul_eq_zero] at h_eq
  exact h_eq.resolve_right hv_ne

lemma ic_nil_pow_s04_apply_thrice (A : Matrix (Fin 3) (Fin 3) ℂ) (mu : ℂ)
    (v : Fin 3 → ℂ) (h_eq : (Matrix.toLin' A) v = mu • v) :
    (Matrix.toLin' A) ((Matrix.toLin' A) ((Matrix.toLin' A) v)) = (mu ^ 3) • v := by
  rw [ic_nil_pow_s03_apply_twice A mu v h_eq]
  rw [LinearMap.map_smul]
  rw [h_eq]
  rw [smul_smul]
  have h_scalar : mu ^ 2 * mu = mu ^ 3 := by ring
  rw [h_scalar]

lemma ic_ker_s01_sub_apply (A : Matrix (Fin 3) (Fin 3) ℂ) (mu : ℂ) (v : Fin 3 → ℂ) :
    let T_pow := (Matrix.toLin' A) ^ 3
    let ScaledId := (mu ^ 3) • (1 : Module.End ℂ (Fin 3 → ℂ))
    (T_pow - ScaledId) v = T_pow v - ScaledId v := by
  intro T_pow ScaledId
  rw [LinearMap.sub_apply]

lemma ic_ker_s02_smul_id_apply (mu : ℂ) (v : Fin 3 → ℂ) :
    ((mu ^ 3) • (1 : Module.End ℂ (Fin 3 → ℂ))) v = (mu ^ 3) • v := by
  simp only [LinearMap.smul_apply]
  aesop

lemma ic_ker_s03_pow3_apply (A : Matrix (Fin 3) (Fin 3) ℂ) (v : Fin 3 → ℂ) :
    ((Matrix.toLin' A) ^ 3) v = (Matrix.toLin' A) ((Matrix.toLin' A) ((Matrix.toLin' A) v)) := by
  rfl

lemma ic_ker_s04_expand_all (A : Matrix (Fin 3) (Fin 3) ℂ) (mu : ℂ) (v : Fin 3 → ℂ) :
    let T := (Matrix.toLin' A ^ 3) - (mu ^ 3) • 1
    T v = (Matrix.toLin' A) ((Matrix.toLin' A) ((Matrix.toLin' A) v)) - (mu ^ 3) • v := by
  intro T
  dsimp only [T]
  rw [ic_ker_s01_sub_apply A mu v]
  rw [ic_ker_s02_smul_id_apply mu v]
  rw [ic_ker_s03_pow3_apply A v]

lemma ic_nil_pow_s05_kernel_eq (A : Matrix (Fin 3) (Fin 3) ℂ) (mu : ℂ) (v : Fin 3 → ℂ)
    (h : (Matrix.toLin' A) ((Matrix.toLin' A) ((Matrix.toLin' A) v)) = (mu ^ 3) • v) :
    let T : Module.End ℂ (Fin 3 → ℂ) := (Matrix.toLin' A ^ 3) - (mu ^ 3) • 1
    T v = 0 := by
  intro T
  rw [ic_ker_s04_expand_all A mu v]
  rw [h]
  rw [sub_self]

lemma ic_peig_s01_pow3_def (A : Matrix (Fin 3) (Fin 3) ℂ) (v : Fin 3 → ℂ) :
    ((Matrix.toLin' A) ^ 3) v = (Matrix.toLin' A) ((Matrix.toLin' A) ((Matrix.toLin' A) v)) := by
  rfl

lemma ic_peig_s02_calc_image (A : Matrix (Fin 3) (Fin 3) ℂ) (mu : ℂ) (v : Fin 3 → ℂ)
    (h_eig : (Matrix.toLin' A) v = mu • v) :
    ((Matrix.toLin' A) ^ 3) v = (mu ^ 3) • v := by
  rw [ic_peig_s01_pow3_def]
  exact ic_nil_pow_s04_apply_thrice A mu v h_eig

lemma ic_peig_s03_mem_space (f : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ)) (lam : ℂ) (v : Fin 3 → ℂ)
    (h_eq : f v = lam • v) :
    v ∈ Module.End.eigenspace f lam := by
  rw [Module.End.mem_eigenspace_iff]
  exact h_eq

lemma ic_peig_s04_has_eigenvalue (f : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ)) (lam : ℂ) (v : Fin 3 → ℂ)
    (hv_ne : v ≠ 0) (hv_mem : v ∈ Module.End.eigenspace f lam) :
    Module.End.HasEigenvalue f lam := by
  rw [Module.End.HasEigenvalue]
  intro h_bot
  aesop

lemma ic_nil_s02_pow_eigen (A : Matrix (Fin 3) (Fin 3) ℂ) (mu : ℂ) 
    (h_mu : Module.End.HasEigenvalue (Matrix.toLin' A) mu) :
    Module.End.HasEigenvalue ((Matrix.toLin' A) ^ 3) (mu ^ 3) := by
  rcases ic_nil_pow_s01_get_eigenvector A mu h_mu with ⟨v, hv_ne, hv_eq⟩
  have h_pow_eq := ic_peig_s02_calc_image A mu v hv_eq
  have h_mem := ic_peig_s03_mem_space ((Matrix.toLin' A) ^ 3) (mu ^ 3) v h_pow_eq
  exact ic_peig_s04_has_eigenvalue ((Matrix.toLin' A) ^ 3) (mu ^ 3) v hv_ne h_mem

lemma ic_nil_s03_zero_map_eigen (mu : ℂ) 
    (h_eig : Module.End.HasEigenvalue (0 : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ)) mu) :
    mu = 0 := by
  have h_ne_bot := ic_zero_s01_ne_bot mu h_eig
  rcases ic_zero_s02_exists_v mu h_ne_bot with ⟨v, hv_ne, hv_mem⟩
  have h_eq_map := ic_zero_s03_mem_iff mu v hv_mem
  have h_eq_zero := ic_zero_s04_apply_zero mu v h_eq_map
  exact ic_zero_s05_solve mu v hv_ne h_eq_zero

lemma ic_nil_s04_scalar_root (mu : ℂ) (h : mu ^ 3 = 0) : mu = 0 := by
  exact eq_zero_of_pow_eq_zero h

lemma ic_B01_nilpotent_eigenvalues (A : Matrix (Fin 3) (Fin 3) ℂ) (h : A ^ 3 = 0) :
    ∀ mu, Module.End.HasEigenvalue (Matrix.toLin' A) mu → mu = 0 := by
  intro mu h_mu
  have h_pow_eig := ic_nil_s02_pow_eigen A mu h_mu
  rw [ic_nil_s01_map_pow_zero A h] at h_pow_eig
  have h_mu3_zero := ic_nil_s03_zero_map_eigen (mu ^ 3) h_pow_eig
  exact ic_nil_s04_scalar_root mu h_mu3_zero

variable {n : Type*} [Fintype n] [DecidableEq n]

def IsSchurUpperTriangular {n : Type*} [Preorder n] (M : Matrix n n ℂ) : Prop :=
  ∀ i j, j < i → M i j = 0

namespace Matrix
abbrev IsUpperTriangular {n : Type*} [Preorder n] (M : Matrix n n ℂ) : Prop :=
  IsSchurUpperTriangular M
end Matrix

lemma ic_schur_s01_iso_exists :
    FiniteDimensional ℂ (EuclideanSpace ℂ (Fin 3)) := by
  infer_instance

noncomputable def ic_schur_s02_inner_space :
    InnerProductSpace ℂ (EuclideanSpace ℂ (Fin 3)) := by
  infer_instance

noncomputable def ic_schur_s03_a_inner_product_space :
    InnerProductSpace ℂ (EuclideanSpace ℂ (Fin 3)) := by
  infer_instance

lemma ic_schur_s03_b_finite_dimensional :
    FiniteDimensional ℂ (EuclideanSpace ℂ (Fin 3)) := by
  infer_instance

section SchurDecomposition3D

-- Step 1: Normalize eigenvector to unit length
lemma ic_schur_s03_eigenvector_normalized (u : EuclideanSpace ℂ (Fin 3)) (hu_ne : u ≠ 0) :
    let u0 := (‖u‖)⁻¹ • u
    ‖u0‖ = 1 := by
  intro u0
  have hu_norm_ne : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu_ne
  calc
    ‖u0‖ = ‖(‖u‖ : ℂ)⁻¹‖ * ‖u‖ := by simp [u0, norm_smul]
    _ = (‖u‖)⁻¹ * ‖u‖ := by simp
    _ = 1 := by simp [hu_norm_ne]

-- Step 2: Show T-invariance of orthogonal complement
lemma ic_schur_s03_adjoint_invariant (T : EuclideanSpace ℂ (Fin 3) →L[ℂ] EuclideanSpace ℂ (Fin 3))
    (u : EuclideanSpace ℂ (Fin 3)) (μ : ℂ) (hu_eq : T.adjoint u = μ • u) :
    ∀ x ∈ Submodule.orthogonal (Submodule.span ℂ {u}), 
      T x ∈ Submodule.orthogonal (Submodule.span ℂ {u}) := by
  intro x hx
  rw [Submodule.mem_orthogonal] at hx ⊢
  intro y hy
  rw [Submodule.mem_span_singleton] at hy
  rcases hy with ⟨c, rfl⟩
  calc
    ⟪c • u, T x⟫ = star c * ⟪u, T x⟫ := by simp []; ring
    _ = star c * ⟪T.adjoint u, x⟫ := by rw [ContinuousLinearMap.adjoint_inner_left]
    _ = star c * ⟪μ • u, x⟫ := by rw [hu_eq]
    _ = star c * (star μ * ⟪u, x⟫) := by simp []; aesop
    _ = 0 := by
      have h := hx u (Submodule.mem_span_singleton_self u)
      simp [h]

lemma ic_schur_s03_restrict (T : EuclideanSpace ℂ (Fin 3) →L[ℂ] EuclideanSpace ℂ (Fin 3))
    (S : Submodule ℂ (EuclideanSpace ℂ (Fin 3)))
    (h_inv : ∀ x, x ∈ S → T x ∈ S) :
    ∃ T' : S →L[ℂ] S, ∀ x : S, (T x : EuclideanSpace ℂ (Fin 3)) = T' x := by
  use (T.toLinearMap.restrict h_inv).toContinuousLinearMap
  intro x
  rfl

-- Step 4: Get orthonormal basis for 1-dim subspace
lemma ic_basis_s01_ne_zero (u : EuclideanSpace ℂ (Fin 3)) (hu_norm : ‖u‖ = 1) : 
    u ≠ 0 := by
  intro h
  simp [h] at hu_norm

lemma ic_basis_s02_smul_eq_zero (u : EuclideanSpace ℂ (Fin 3)) (hu_ne : u ≠ 0) (c : ℂ) 
    (h : c • u = 0) : c = 0 := by
  rw [smul_eq_zero] at h
  cases h with
  | inl h_c => exact h_c
  | inr h_u => contradiction

lemma ic_basis_s03_linear_independent (u : EuclideanSpace ℂ (Fin 3)) (hu_ne : u ≠ 0) :
    LinearIndependent ℂ (fun (_ : Fin 1) => u) := by
  rw [linearIndependent_iff']
  intro s g h_sum i hi_mem
  fin_cases i
  have h_s_eq : s = {0} := by
    ext x
    fin_cases x
    simp []
    aesop
  rw [h_s_eq] at h_sum
  simp only [Finset.sum_singleton] at h_sum
  exact ic_basis_s02_smul_eq_zero u hu_ne (g 0) h_sum

lemma ic_basis_s04_span_eq (u : EuclideanSpace ℂ (Fin 3)) :
    Submodule.span ℂ (Set.range (fun (_ : Fin 1) => u)) = Submodule.span ℂ {u} := by
  rw [Set.range_const]

noncomputable def ic_basis_s05_basis_on_range (u : EuclideanSpace ℂ (Fin 3)) (hu_ne : u ≠ 0) :
    Basis (Fin 1) ℂ (Submodule.span ℂ (Set.range (fun (_ : Fin 1) => u))) :=
  Basis.span (ic_basis_s03_linear_independent u hu_ne)

noncomputable def ic_basis_s06_01_iso (u : EuclideanSpace ℂ (Fin 3)) :
    Submodule.span ℂ (Set.range (fun (_ : Fin 1) => u)) ≃ₗ[ℂ] Submodule.span ℂ {u} :=
  LinearEquiv.ofEq _ _ (ic_basis_s04_span_eq u)

noncomputable def ic_basis_s05_basis_def (u : EuclideanSpace ℂ (Fin 3)) (hu_ne : u ≠ 0) :
    Basis (Fin 1) ℂ (Submodule.span ℂ {u}) :=
  (ic_basis_s05_basis_on_range u hu_ne).map (ic_basis_s06_01_iso u)

lemma ic_basis_s06_02_range_apply (u : EuclideanSpace ℂ (Fin 3)) (hu_ne : u ≠ 0) :
    (ic_basis_s05_basis_on_range u hu_ne) 0 = 
    ⟨u, Submodule.subset_span (Set.mem_range_self 0)⟩ := by
  simp [ic_basis_s05_basis_on_range]
  aesop

lemma ic_basis_s06_03_iso_apply (u : EuclideanSpace ℂ (Fin 3)) 
    (x : Submodule.span ℂ (Set.range (fun (_ : Fin 1) => u))) :
    (ic_basis_s06_01_iso u) x = ⟨x.1, (ic_basis_s04_span_eq u ▸ x.2)⟩ := by
  rfl

lemma ic_basis_s06_apply (u : EuclideanSpace ℂ (Fin 3)) (hu_ne : u ≠ 0) :
    (ic_basis_s05_basis_def u hu_ne) 0 = ⟨u, Submodule.mem_span_singleton_self u⟩ := by
  simp [ic_basis_s05_basis_def, ic_basis_s06_02_range_apply, ic_basis_s06_03_iso_apply]

lemma ic_basis_s07_inner_self (u : EuclideanSpace ℂ (Fin 3)) (hu_ne : u ≠ 0) :
    let b := ic_basis_s05_basis_def u hu_ne
    ⟪(b 0 : EuclideanSpace ℂ (Fin 3)), (b 0 : EuclideanSpace ℂ (Fin 3))⟫ = ⟪u, u⟫ := by
  intro b
  rw [ic_basis_s06_apply u hu_ne]
  
lemma ic_basis_s08_01_expand (u : EuclideanSpace ℂ (Fin 3)) : 
    ⟪u, u⟫ = (‖u‖ : ℂ) ^ 2 := by
  rw [inner_self_eq_norm_sq_to_K]
  aesop

lemma ic_basis_s08_02_subst (u : EuclideanSpace ℂ (Fin 3)) (hu_norm : ‖u‖ = 1) :
    (‖u‖ : ℂ) ^ 2 = (1 : ℂ) ^ 2 := by
  rw [hu_norm]
  aesop

lemma ic_basis_s08_norm_sq (u : EuclideanSpace ℂ (Fin 3)) (hu_norm : ‖u‖ = 1) :
    ⟪u, u⟫ = (1 : ℂ) := by
  rw [ic_basis_s08_01_expand]
  rw [ic_basis_s08_02_subst u hu_norm]
  simp

lemma ic_basis_s09_01_condition 
    (u : EuclideanSpace ℂ (Fin 3))
    (b : Basis (Fin 1) ℂ (Submodule.span ℂ {u})) :
    Orthonormal ℂ b ↔ ∀ i j, ⟪(b i : EuclideanSpace ℂ (Fin 3)), (b j : EuclideanSpace ℂ (Fin 3))⟫ = if i = j then (1 : ℂ) else 0 := by
  exact orthonormal_iff_ite

lemma ic_basis_s09_02_indices (i j : Fin 1) : i = 0 ∧ j = 0 := by
  constructor <;> apply Subsingleton.elim

lemma ic_basis_s09_03_ite_simp (i j : Fin 1) : 
    (if i = j then (1 : ℂ) else 0) = 1 := by
  have h : i = j := Subsingleton.elim i j
  rw [if_pos h]

lemma ic_basis_s09_04_inner_eq_u (u : EuclideanSpace ℂ (Fin 3)) (hu_ne : u ≠ 0) :
    let b := ic_basis_s05_basis_def u hu_ne
    ⟪(b 0 : EuclideanSpace ℂ (Fin 3)), (b 0 : EuclideanSpace ℂ (Fin 3))⟫ = ⟪u, u⟫ := by
  intro b
  have h_val : (b 0 : EuclideanSpace ℂ (Fin 3)) = u := by
    rw [ic_basis_s06_apply u hu_ne]
  rw [h_val]

lemma ic_basis_s09_05_inner_val (u : EuclideanSpace ℂ (Fin 3)) (hu_norm : ‖u‖ = 1) :
    let b := ic_basis_s05_basis_def u (ic_basis_s01_ne_zero u hu_norm)
    ⟪(b 0 : EuclideanSpace ℂ (Fin 3)), (b 0 : EuclideanSpace ℂ (Fin 3))⟫ = 1 := by
  intro b
  rw [ic_basis_s09_04_inner_eq_u u (ic_basis_s01_ne_zero u hu_norm)]
  exact ic_basis_s08_norm_sq u hu_norm

lemma ic_basis_s09_06_verify_all (u : EuclideanSpace ℂ (Fin 3)) (hu_norm : ‖u‖ = 1) :
    let b := ic_basis_s05_basis_def u (ic_basis_s01_ne_zero u hu_norm)
    ∀ i j, ⟪(b i : EuclideanSpace ℂ (Fin 3)), (b j : EuclideanSpace ℂ (Fin 3))⟫ = if i = j then (1 : ℂ) else 0 := by
  intro b i j
  rw [ic_basis_s09_03_ite_simp i j]
  have hi : i = 0 := Subsingleton.elim i 0
  have hj : j = 0 := Subsingleton.elim j 0
  rw [hi, hj]
  exact ic_basis_s09_05_inner_val u hu_norm

lemma ic_basis_s09_orthonormal (u : EuclideanSpace ℂ (Fin 3)) (hu_norm : ‖u‖ = 1) :
    Orthonormal ℂ (ic_basis_s05_basis_def u (ic_basis_s01_ne_zero u hu_norm)) := by
  rw [ic_basis_s09_01_condition]
  exact ic_basis_s09_06_verify_all u hu_norm

noncomputable def ic_schur_s03_basis_1d (u : EuclideanSpace ℂ (Fin 3)) (hu_norm : ‖u‖ = 1) :
    OrthonormalBasis (Fin 1) ℂ (Submodule.span ℂ {u}) :=
  OrthonormalBasis.mk 
    (ic_basis_s09_orthonormal u hu_norm)
    (le_of_eq (Basis.span_eq (ic_basis_s05_basis_def u (ic_basis_s01_ne_zero u hu_norm))).symm)

lemma ic_schur_s03_basis_1d_apply (u : EuclideanSpace ℂ (Fin 3)) (hu_norm : ‖u‖ = 1) :
    (ic_schur_s03_basis_1d u hu_norm) 0 = ⟨u, Submodule.mem_span_singleton_self u⟩ := by
  simp [ic_schur_s03_basis_1d, OrthonormalBasis.mk]
  apply ic_basis_s06_apply

lemma ic_dim_s01_card_fin3 : Fintype.card (Fin 3) = 3 := by
  simp

lemma ic_dim_s02_space_dim : 
    finrank ℂ (EuclideanSpace ℂ (Fin 3)) = 3 := by
  rw [finrank_euclideanSpace]
  rw [ic_dim_s01_card_fin3]

lemma ic_dim_s03_span_dim (u : EuclideanSpace ℂ (Fin 3)) (hu_ne : u ≠ 0) :
    finrank ℂ (Submodule.span ℂ {u}) = 1 := by
  exact finrank_span_singleton hu_ne

lemma ic_dim_s04_add_thm (S : Submodule ℂ (EuclideanSpace ℂ (Fin 3))) :
    finrank ℂ S + finrank ℂ Sᗮ = 
    finrank ℂ (EuclideanSpace ℂ (Fin 3)) := by
  exact Submodule.finrank_add_finrank_orthogonal S

lemma ic_dim_s05_spec_add (u : EuclideanSpace ℂ (Fin 3)) :
    finrank ℂ (Submodule.span ℂ {u}) + 
    finrank ℂ (Submodule.span ℂ {u})ᗮ = 
    finrank ℂ (EuclideanSpace ℂ (Fin 3)) := by
  exact ic_dim_s04_add_thm (Submodule.span ℂ {u})

lemma ic_dim_s06_subst_right (u : EuclideanSpace ℂ (Fin 3)) :
    finrank ℂ (Submodule.span ℂ {u}) + 
    finrank ℂ (Submodule.span ℂ {u})ᗮ = 3 := by
  rw [ic_dim_s05_spec_add]
  rw [ic_dim_s02_space_dim]

lemma ic_dim_s07_subst_left (u : EuclideanSpace ℂ (Fin 3)) (hu_ne : u ≠ 0) :
    1 + finrank ℂ (Submodule.span ℂ {u})ᗮ = 3 := by
  rw [← ic_dim_s03_span_dim u hu_ne]
  exact ic_dim_s06_subst_right u

lemma ic_dim_s08_arithmetic (n : ℕ) (h : 1 + n = 3) : n = 2 := by
  exact Nat.add_left_cancel h

lemma ic_dim_s09_calc (u : EuclideanSpace ℂ (Fin 3)) (hu_ne : u ≠ 0) :
    finrank ℂ (Submodule.span ℂ {u})ᗮ = 2 := by
  apply ic_dim_s08_arithmetic
  exact ic_dim_s07_subst_left u hu_ne

lemma ic_schur_s03_dim_orthogonal (u : EuclideanSpace ℂ (Fin 3)) (hu_ne : u ≠ 0) :
    let S := (Submodule.span ℂ {u})ᗮ
    finrank ℂ S = 2 := by
  intro S
  exact ic_dim_s09_calc u hu_ne

lemma ic_2d_s01_eigenvalue (S : Submodule ℂ (EuclideanSpace ℂ (Fin 3)))
    (hS : finrank ℂ S = 2)
    (T : S →L[ℂ] S) :
    ∃ μ : ℂ, Module.End.HasEigenvalue T.toLinearMap μ := by
  haveI : FiniteDimensional ℂ S := FiniteDimensional.of_finrank_eq_succ hS
  haveI : Nontrivial S := nontrivial_of_finrank_eq_succ hS
  exact Module.End.exists_eigenvalue T.toLinearMap

lemma ic_2d_s02_eigenvector (S : Submodule ℂ (EuclideanSpace ℂ (Fin 3)))
    (hS : finrank ℂ S = 2)
    (T : S →L[ℂ] S) :
    ∃ (μ : ℂ) (u : S), ‖u‖ = 1 ∧ T u = μ • u := by
  rcases ic_2d_s01_eigenvalue S hS T with ⟨μ, hμ⟩
  rcases Module.End.HasEigenvalue.exists_hasEigenvector hμ with ⟨v, hv_ne, hv_eq⟩
  let u := (‖v‖ : ℂ)⁻¹ • v
  use μ, u
  constructor
  · have hv_norm_ne : ‖v‖ ≠ 0 := by
      intro h
      apply hv_eq
      simpa using h
    simp [u, norm_smul]
    field_simp [hv_norm_ne]
    aesop
  · simp only [u]
    have h_eig : T v = μ • v := by 
      simpa using hv_ne
    simp [h_eig]
    rw [smul_comm]

lemma ic_2d_s03_01_span_dim 
    (S : Submodule ℂ (EuclideanSpace ℂ (Fin 3)))
    (u : S) (hu_ne : u ≠ 0) :
    finrank ℂ (Submodule.span ℂ {u}) = 1 := by
  exact finrank_span_singleton hu_ne

noncomputable local instance : InnerProductSpace ℂ (EuclideanSpace ℂ (Fin 3)) :=
  PiLp.innerProductSpace (fun _ : Fin 3 => ℂ)

lemma ic_2d_s03_02_ortho_add 
    (S : Submodule ℂ (EuclideanSpace ℂ (Fin 3)))
    (hS : finrank ℂ S = 2)
    (K : Submodule ℂ S) :
    finrank ℂ K + finrank ℂ (Submodule.orthogonal (𝕜 := ℂ) (E := S) K) = 2 := by
  simpa [hS] using (Submodule.finrank_add_finrank_orthogonal (K := K) :
    finrank ℂ K + finrank ℂ Kᗮ = finrank ℂ S)
  
lemma ic_2d_s03_ortho_dim (S : Submodule ℂ (EuclideanSpace ℂ (Fin 3)))
    (hS : finrank ℂ S = 2)
    (u : S) (hu_ne : u ≠ 0) :
    finrank ℂ ((Submodule.span ℂ ({u} : Set S)).orthogonal : Submodule ℂ S) = 1 := by
  have h_add := ic_2d_s03_02_ortho_add S hS (Submodule.span ℂ ({u} : Set S))
  rw [finrank_span_singleton hu_ne] at h_add
  exact Nat.add_left_cancel h_add

lemma ic_schur_s03_schur_2d (S : Submodule ℂ (EuclideanSpace ℂ (Fin 3)))
    (hS : finrank ℂ S = 2)
    (T : S →L[ℂ] S) :
    ∃ b : OrthonormalBasis (Fin 2) ℂ S, (LinearMap.toMatrix b.toBasis b.toBasis T).IsUpperTriangular := by
  classical
  haveI : FiniteDimensional ℂ S := inferInstance
  obtain ⟨μ, u, hu_norm, hTu⟩ := ic_2d_s02_eigenvector S hS T
  let v : Fin 2 → S := fun i => if i = 0 then u else 0
  let s : Set (Fin 2) := {0}
  have hv : Orthonormal ℂ (s.restrict v) := by
    refine ⟨?_, ?_⟩
    · intro i
      rcases i with ⟨i, hi⟩
      have : i = 0 := by simpa [s] using hi
      subst this
      simp [v, hu_norm, s]
    · intro i j hij
      have : i = j := Subsingleton.elim i j
      exact (hij this).elim
  have hcard : finrank ℂ S = Fintype.card (Fin 2) := by
    simp [hS]
  obtain ⟨b, hb⟩ :=
    (Orthonormal.exists_orthonormalBasis_extension_of_card_eq (𝕜 := ℂ)
      (E := S) (ι := Fin 2) (v := v) (s := s) hcard hv)
  have hb0 : b 0 = u := by
    have : (0 : Fin 2) ∈ s := by simp [s]
    simpa [v, s] using hb 0 this
  refine ⟨b, ?_⟩
  intro i j hij
  have hij' : (j : ℕ) < i := (Fin.lt_def).1 hij
  have hi_eq : (i : ℕ) = 1 := by
    apply Nat.eq_of_lt_succ_of_not_lt
    · simp [i.is_lt]
    · intro hi_lt
      have : (i : ℕ) = 0 := Nat.lt_one_iff.mp hi_lt
      have hij0 := hij'
      simp [this] at hij0
  have hj_eq : (j : ℕ) = 0 := by
    have : (j : ℕ) < 1 := by simpa [hi_eq] using hij'
    exact Nat.lt_one_iff.mp this
  have hi : i = ⟨1, by decide⟩ := by
    apply Fin.ext
    simp [hi_eq]
  have hj : j = ⟨0, by decide⟩ := by
    apply Fin.ext
    simp [hj_eq]
  subst hi hj
  have h_entry : (LinearMap.toMatrix b.toBasis b.toBasis T) 1 0 = ⟪b 1, T (b 0)⟫ := by
    calc
      (LinearMap.toMatrix b.toBasis b.toBasis T) 1 0
          = (b.toBasis.repr (T (b 0))) 1 :=
            (LinearMap.toMatrix_apply (v₁ := b.toBasis) (v₂ := b.toBasis) (f := T) (i := 1) (j := 0))
      _ = b.repr (T (b 0)) 1 := by
        exact OrthonormalBasis.coe_toBasis_repr_apply
          (b := b) (x := T (b 0)) (i := (1 : Fin 2))
      _ = ⟪b 1, T (b 0)⟫ := by
        simpa using (OrthonormalBasis.repr_apply_apply (b := b) (v := T (b 0)) (i := 1))
  have hTu' : T (b 0) = μ • (b 0) := by
    simpa [hb0] using hTu
  have horth : ⟪b 1, b 0⟫ = 0 := by
    have hpair := (b.orthonormal).2
    exact hpair (i := (1 : Fin 2)) (j := (0 : Fin 2)) (by decide)
  have hzero : ⟪b 1, T (b 0)⟫ = 0 := by
    calc
      ⟪b 1, T (b 0)⟫ = ⟪b 1, μ • b 0⟫ := by simp [hTu']
      _ = μ * ⟪b 1, b 0⟫ := by simp [(inner_smul_right (b 1) (b 0) μ)]
      _ = 0 := by simp [horth]
  have : (LinearMap.toMatrix b.toBasis b.toBasis T) 1 0 = 0 := by
    simp [h_entry, hzero]
  simpa [Matrix.IsUpperTriangular, IsSchurUpperTriangular] using this
section SchurStep7And8

open scoped ComplexInnerProductSpace

noncomputable def ic_schur_s03_combined_vec
    (u : E3) (S : Submodule ℂ E3) (b₂ : OrthonormalBasis (Fin 2) ℂ S) : Fin 3 → E3 :=
  fun i => Fin.cases (b₂ 0 : E3) (fun i => Fin.cases (b₂ 1 : E3) (fun _ => u) i) i

@[simp] lemma ic_schur_s03_combined_vec_apply0
    (u : E3) (S : Submodule ℂ E3) (b₂ : OrthonormalBasis (Fin 2) ℂ S) :
    ic_schur_s03_combined_vec u S b₂ 0 = (b₂ 0 : E3) := rfl

@[simp] lemma ic_schur_s03_combined_vec_apply1
    (u : E3) (S : Submodule ℂ E3) (b₂ : OrthonormalBasis (Fin 2) ℂ S) :
    ic_schur_s03_combined_vec u S b₂ 1 = (b₂ 1 : E3) := rfl

@[simp] lemma ic_schur_s03_combined_vec_apply2
    (u : E3) (S : Submodule ℂ E3) (b₂ : OrthonormalBasis (Fin 2) ℂ S) :
    ic_schur_s03_combined_vec u S b₂ 2 = u := rfl

lemma ic_schur_s03_b2_mem_orthogonal
    (u : E3) (S : Submodule ℂ E3) (hS : S = (Submodule.span ℂ {u})ᗮ)
    (b₂ : OrthonormalBasis (Fin 2) ℂ S) (i : Fin 2) :
    (b₂ i : E3) ∈ (Submodule.span ℂ {u})ᗮ := by
  simpa [hS] using (b₂ i).property

lemma ic_schur_s03_inner_u_b2
    (u : E3) (_hu_norm : ‖u‖ = 1)
    (S : Submodule ℂ E3) (hS : S = (Submodule.span ℂ {u})ᗮ)
    (b₂ : OrthonormalBasis (Fin 2) ℂ S) (i : Fin 2) :
    ⟪u, (b₂ i : E3)⟫ = 0 := by
  have hb2 : (b₂ i : E3) ∈ (Submodule.span ℂ {u})ᗮ :=
    ic_schur_s03_b2_mem_orthogonal u S hS b₂ i
  have hu_mem : (u : E3) ∈ Submodule.span ℂ ({u} : Set E3) :=
    Submodule.mem_span_singleton_self u
  exact (Submodule.mem_orthogonal (Submodule.span ℂ ({u} : Set E3)) (b₂ i : E3)).1 hb2 u hu_mem

lemma ic_schur_s03_inner_b2_u
    (u : E3) (hu_norm : ‖u‖ = 1)
    (S : Submodule ℂ E3) (hS : S = (Submodule.span ℂ {u})ᗮ)
    (b₂ : OrthonormalBasis (Fin 2) ℂ S) (i : Fin 2) :
    ⟪(b₂ i : E3), u⟫ = 0 := by
  exact (inner_eq_zero_symm).1 (ic_schur_s03_inner_u_b2 u hu_norm S hS b₂ i)

lemma ic_schur_s03_combined_vec_norm
    (u : E3) (hu_norm : ‖u‖ = 1)
    (S : Submodule ℂ E3) (b₂ : OrthonormalBasis (Fin 2) ℂ S) :
    ∀ i, ‖ic_schur_s03_combined_vec u S b₂ i‖ = 1 := by
  intro i
  fin_cases i
  · simp [ic_schur_s03_combined_vec]
    rw [Submodule.norm_coe]
    exact b₂.orthonormal.1 0
  · simp [ic_schur_s03_combined_vec] 
    exact b₂.orthonormal.1 1
  · simpa [ic_schur_s03_combined_vec] using hu_norm

lemma ic_schur_s03_combined_vec_pairwise
    (u : E3) (hu_norm : ‖u‖ = 1)
    (S : Submodule ℂ E3) (hS : S = (Submodule.span ℂ {u})ᗮ)
    (b₂ : OrthonormalBasis (Fin 2) ℂ S) :
    Pairwise fun i j => ⟪ic_schur_s03_combined_vec u S b₂ i, ic_schur_s03_combined_vec u S b₂ j⟫ = 0 := by
  classical
  intro i j hij
  fin_cases i <;> fin_cases j
  · cases hij rfl
  · have h := (b₂.orthonormal).2 (i := (0 : Fin 2)) (j := (1 : Fin 2)) (by decide)
    simpa [ic_schur_s03_combined_vec] using (Submodule.coe_inner S (b₂ 0) (b₂ 1)).symm.trans h
  · -- (0,2)
    simpa [ic_schur_s03_combined_vec] using ic_schur_s03_inner_b2_u u hu_norm S hS b₂ 0
  · -- (1,0)
    have h := (b₂.orthonormal).2 (i := (1 : Fin 2)) (j := (0 : Fin 2)) (by decide)
    simpa [ic_schur_s03_combined_vec] using (Submodule.coe_inner S (b₂ 1) (b₂ 0)).symm.trans h
  · cases hij rfl
  · -- (1,2)
    simpa [ic_schur_s03_combined_vec] using ic_schur_s03_inner_b2_u u hu_norm S hS b₂ 1
  · -- (2,0)
    simpa [ic_schur_s03_combined_vec] using ic_schur_s03_inner_u_b2 u hu_norm S hS b₂ 0
  · -- (2,1)
    simpa [ic_schur_s03_combined_vec] using ic_schur_s03_inner_u_b2 u hu_norm S hS b₂ 1
  · cases hij rfl

lemma ic_schur_s03_combined_vec_orthonormal
    (u : E3) (hu_norm : ‖u‖ = 1)
    (S : Submodule ℂ E3) (hS : S = (Submodule.span ℂ {u})ᗮ)
    (b₂ : OrthonormalBasis (Fin 2) ℂ S) :
    Orthonormal ℂ (ic_schur_s03_combined_vec u S b₂) := by
  refine ⟨ic_schur_s03_combined_vec_norm u hu_norm S b₂, ic_schur_s03_combined_vec_pairwise u hu_norm S hS b₂⟩

lemma ic_schur_s03_combined_vec_span_top
    (u : E3) (hu_norm : ‖u‖ = 1)
    (S : Submodule ℂ E3) (hS : S = (Submodule.span ℂ {u})ᗮ)
    (b₂ : OrthonormalBasis (Fin 2) ℂ S) :
    Submodule.span ℂ (Set.range (ic_schur_s03_combined_vec u S b₂)) = ⊤ := by
  classical
  have hv : Orthonormal ℂ (ic_schur_s03_combined_vec u S b₂) :=
    ic_schur_s03_combined_vec_orthonormal u hu_norm S hS b₂
  have hli : LinearIndependent ℂ (ic_schur_s03_combined_vec u S b₂) :=
    Orthonormal.linearIndependent hv
  have hcard : Fintype.card (Fin 3) = finrank ℂ E3 := by
    simp []
  exact hli.span_eq_top_of_card_eq_finrank' hcard

noncomputable def ic_schur_s03_combined_basis
    (u : E3) (hu_norm : ‖u‖ = 1)
    (S : Submodule ℂ E3) (hS : S = (Submodule.span ℂ {u})ᗮ)
    (b₂ : OrthonormalBasis (Fin 2) ℂ S) : OrthonormalBasis (Fin 3) ℂ E3 := by
  classical
  refine OrthonormalBasis.mk (ic_schur_s03_combined_vec_orthonormal u hu_norm S hS b₂) ?_
  rw [ic_schur_s03_combined_vec_span_top u hu_norm S hS b₂]

lemma ic_schur_s03_combine_bases_def (u : E3) (hu_norm : ‖u‖ = 1)
    (S : Submodule ℂ E3)
    (hS : S = (Submodule.span ℂ {u})ᗮ)
    (_b₁ : OrthonormalBasis (Fin 1) ℂ (Submodule.span ℂ {u}))
    (b₂ : OrthonormalBasis (Fin 2) ℂ S) :
    let b := ic_schur_s03_combined_basis u hu_norm S hS b₂
    b = b := rfl

lemma ic_schur_s03_invariant_of_eq
    (T : E3 →L[ℂ] E3) (u : E3) (μ : ℂ) (h_adj : T.adjoint u = μ • u)
    (S : Submodule ℂ E3) (hS : S = (Submodule.span ℂ {u})ᗮ) :
    ∀ x, x ∈ S → T x ∈ S := by
  intro x hx
  have hx' : x ∈ (Submodule.span ℂ ({u} : Set E3))ᗮ := by
    simpa [hS] using hx
  have hTx' : T x ∈ (Submodule.span ℂ ({u} : Set E3))ᗮ :=
    ic_schur_s03_adjoint_invariant T u μ h_adj x hx'
  simpa [hS] using hTx'

noncomputable def ic_schur_s03_restrict_to_S
    (T : E3 →L[ℂ] E3) (u : E3) (μ : ℂ) (h_adj : T.adjoint u = μ • u)
    (S : Submodule ℂ E3) (hS : S = (Submodule.span ℂ {u})ᗮ) : S →ₗ[ℂ] S :=
  T.toLinearMap.restrict (p := S) (q := S) (ic_schur_s03_invariant_of_eq T u μ h_adj S hS)

@[simp] lemma ic_schur_s03_restrict_to_S_apply
    (T : E3 →L[ℂ] E3) (u : E3) (μ : ℂ) (h_adj : T.adjoint u = μ • u)
    (S : Submodule ℂ E3) (hS : S = (Submodule.span ℂ {u})ᗮ) (x : S) :
    ((ic_schur_s03_restrict_to_S T u μ h_adj S hS x : S) : E3) = T x := rfl

lemma ic_schur_s03_toMatrix_entry_eq_inner
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℂ E) (T : E →ₗ[ℂ] E) (i j : ι) :
    (LinearMap.toMatrix b.toBasis b.toBasis T) i j = ⟪b i, T (b j)⟫ := by
  calc
    (LinearMap.toMatrix b.toBasis b.toBasis T) i j
        = (b.toBasis.repr (T (b j))) i :=
          (LinearMap.toMatrix_apply (v₁ := b.toBasis) (v₂ := b.toBasis) (f := T) (i := i) (j := j))
    _ = b.repr (T (b j)) i := by
      exact OrthonormalBasis.coe_toBasis_repr_apply (b := b) (x := T (b j)) (i := i)
    _ = ⟪b i, T (b j)⟫ := by
      simpa using (OrthonormalBasis.repr_apply_apply (b := b) (v := T (b j)) (i := i))

lemma ic_schur_s03_fin3_lt_cases {i j : Fin 3} (hij : j < i) :
    (i = (1 : Fin 3) ∧ j = 0) ∨ (i = 2 ∧ j = 0) ∨ (i = 2 ∧ j = 1) := by
  fin_cases i <;> fin_cases j
  · exact (False.elim ((by decide : ¬ ((0 : Fin 3) < 0)) hij))
  · exact (False.elim ((by decide : ¬ ((1 : Fin 3) < 0)) hij))
  · exact (False.elim ((by decide : ¬ ((2 : Fin 3) < 0)) hij))
  · exact Or.inl ⟨rfl, rfl⟩
  · exact (False.elim ((by decide : ¬ ((1 : Fin 3) < 1)) hij))
  · exact (False.elim ((by decide : ¬ ((2 : Fin 3) < 1)) hij))
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  · exact (False.elim ((by decide : ¬ ((2 : Fin 3) < 2)) hij))

lemma ic_schur_s03_hb₂10_inner
    (T : E3 →L[ℂ] E3) (u : E3) (μ : ℂ) (h_adj : T.adjoint u = μ • u)
    (S : Submodule ℂ E3) (hS : S = (Submodule.span ℂ {u})ᗮ)
    (b₂ : OrthonormalBasis (Fin 2) ℂ S)
    (hb₂ :
      (LinearMap.toMatrix b₂.toBasis b₂.toBasis
        (ic_schur_s03_restrict_to_S T u μ h_adj S hS)).IsUpperTriangular) :
    ⟪(b₂ 1 : E3), T (b₂ 0 : E3)⟫ = 0 := by
  classical
  have hentry :=
    ic_schur_s03_toMatrix_entry_eq_inner (b := b₂)
      (T := (ic_schur_s03_restrict_to_S T u μ h_adj S hS)) (i := (1 : Fin 2))
      (j := (0 : Fin 2))
  have hmat :
      (LinearMap.toMatrix b₂.toBasis b₂.toBasis
        (ic_schur_s03_restrict_to_S T u μ h_adj S hS)) 1 0 = 0 :=
    hb₂ 1 0 (by decide)
  have hinnerS :
      ⟪b₂ 1, (ic_schur_s03_restrict_to_S T u μ h_adj S hS) (b₂ 0)⟫ = 0 := by
    simpa [hentry] using hmat
  have hcoe :
      ⟪(b₂ 1 : E3),
          (((ic_schur_s03_restrict_to_S T u μ h_adj S hS) (b₂ 0) : S) : E3)⟫ = 0 := by
    simpa using (Submodule.coe_inner S (b₂ 1)
      ((ic_schur_s03_restrict_to_S T u μ h_adj S hS) (b₂ 0))).symm.trans hinnerS
  simpa using hcoe

lemma ic_schur_s03_inner_u_T_b₂
    (T : E3 →L[ℂ] E3) (u : E3) (μ : ℂ) (h_adj : T.adjoint u = μ • u)
    (S : Submodule ℂ E3) (hS : S = (Submodule.span ℂ {u})ᗮ)
    (b₂ : OrthonormalBasis (Fin 2) ℂ S) (i : Fin 2) :
    ⟪u, T (b₂ i : E3)⟫ = 0 := by
  have hb2_mem : (b₂ i : E3) ∈ (Submodule.span ℂ ({u} : Set E3))ᗮ :=
    ic_schur_s03_b2_mem_orthogonal u S hS b₂ i
  have hT_mem : T (b₂ i : E3) ∈ (Submodule.span ℂ ({u} : Set E3))ᗮ :=
    ic_schur_s03_adjoint_invariant T u μ h_adj (b₂ i : E3) hb2_mem
  have hu_mem : (u : E3) ∈ Submodule.span ℂ ({u} : Set E3) :=
    Submodule.mem_span_singleton_self u
  exact (Submodule.mem_orthogonal (Submodule.span ℂ ({u} : Set E3)) (T (b₂ i : E3))).1 hT_mem u hu_mem

lemma ic_schur_s03_upper_triangular_verification
    (T : EuclideanSpace ℂ (Fin 3) →L[ℂ] EuclideanSpace ℂ (Fin 3))
    (u : EuclideanSpace ℂ (Fin 3)) (hu_norm : ‖u‖ = 1)
    (μ : ℂ) (h_adj : T.adjoint u = μ • u)
    (S : Submodule ℂ (EuclideanSpace ℂ (Fin 3)))
    (hS : S = (Submodule.span ℂ {u})ᗮ)
    (b₂ : OrthonormalBasis (Fin 2) ℂ S)
    (hb₂ : (LinearMap.toMatrix b₂.toBasis b₂.toBasis
      (ic_schur_s03_restrict_to_S T u μ h_adj S hS)).IsUpperTriangular) :
    let b := ic_schur_s03_combined_basis u hu_norm S hS b₂
    (LinearMap.toMatrix b.toBasis b.toBasis T).IsUpperTriangular := by
  intro b
  classical
  have hb0 : b 0 = (b₂ 0 : E3) := by
    simp [b, ic_schur_s03_combined_basis]
  have hb1 : b 1 = (b₂ 1 : E3) := by
    simp [b, ic_schur_s03_combined_basis]
  have hb2 : b 2 = u := by
    simp [b, ic_schur_s03_combined_basis]
  intro i j hij
  rcases ic_schur_s03_fin3_lt_cases hij with h10 | h20 | h21
  · rcases h10 with ⟨rfl, rfl⟩
    have h_inner : ⟪(b₂ 1 : E3), T (b₂ 0 : E3)⟫ = 0 :=
      ic_schur_s03_hb₂10_inner T u μ h_adj S hS b₂ hb₂
    have h_entry := ic_schur_s03_toMatrix_entry_eq_inner (b := b) (T := T) (i := (1 : Fin 3)) (j := 0)
    simp [h_entry, hb0, hb1, h_inner]
  · rcases h20 with ⟨rfl, rfl⟩
    have h_inner : ⟪u, T (b₂ 0 : E3)⟫ = 0 :=
      ic_schur_s03_inner_u_T_b₂ T u μ h_adj S hS b₂ 0
    have h_entry := ic_schur_s03_toMatrix_entry_eq_inner (b := b) (T := T) (i := (2 : Fin 3)) (j := 0)
    simp [h_entry, hb0, hb2, h_inner]
  · rcases h21 with ⟨rfl, rfl⟩
    have h_inner : ⟪u, T (b₂ 1 : E3)⟫ = 0 :=
      ic_schur_s03_inner_u_T_b₂ T u μ h_adj S hS b₂ 1
    have h_entry := ic_schur_s03_toMatrix_entry_eq_inner (b := b) (T := T) (i := (2 : Fin 3)) (j := 1)
    simp [h_entry, hb1, hb2, h_inner]

end SchurStep7And8

lemma ic_schur_s03_apply_schur_thm (A : Matrix (Fin 3) (Fin 3) ℂ) :
    let T := Matrix.toEuclideanLin A
    ∃ b : OrthonormalBasis (Fin 3) ℂ (EuclideanSpace ℂ (Fin 3)),
      (LinearMap.toMatrix b.toBasis b.toBasis T).IsUpperTriangular := by
  classical
  intro T
  let T : EuclideanSpace ℂ (Fin 3) →L[ℂ] EuclideanSpace ℂ (Fin 3) := LinearMap.toContinuousLinearMap T
  haveI : FiniteDimensional ℂ (EuclideanSpace ℂ (Fin 3)) := ic_schur_s01_iso_exists
  haveI : Nontrivial (EuclideanSpace ℂ (Fin 3)) := by infer_instance
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue T.adjoint.toLinearMap
  obtain ⟨u, hu⟩ := hμ.exists_hasEigenvector
  have hu_ne : u ≠ 0 := hu.2
  have hu_eq : T.adjoint u = μ • u := hu.apply_eq_smul
  let u0 := (‖u‖)⁻¹ • u
  have hu0_norm : ‖u0‖ = 1 := ic_schur_s03_eigenvector_normalized u hu_ne
  have hu0_eq : T.adjoint u0 = μ • u0 := by
    simp [u0, hu_eq]
    rw [smul_comm]
  let S := (Submodule.span ℂ {u})ᗮ
  have hS_dim : finrank ℂ S = 2 := ic_schur_s03_dim_orthogonal u hu_ne
  have hS_eq : S = (ℂ ∙ u0)ᗮ := by
    have h_span : (ℂ ∙ u) = (ℂ ∙ u0) := by
      simp [u0]
      apply le_antisymm
      · rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
        use ‖u‖
        simp [smul_smul, hu_ne]
      · rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
        use ‖u‖⁻¹
        aesop
    simp [S, h_span]
  let T_S : S →L[ℂ] S := LinearMap.toContinuousLinearMap (ic_schur_s03_restrict_to_S T u0 μ hu0_eq S hS_eq)
  obtain ⟨b₂, hb₂_upper⟩ := ic_schur_s03_schur_2d S hS_dim T_S
  let b := ic_schur_s03_combined_basis u0 hu0_norm S hS_eq b₂
  use b
  have h_result := ic_schur_s03_upper_triangular_verification T u0 hu0_norm μ hu0_eq S hS_eq b₂ hb₂_upper
  simp [T] at h_result ⊢
  exact h_result
      
end SchurDecomposition3D


noncomputable def ic_schur_s04_get_basis (A : Matrix (Fin 3) (Fin 3) ℂ) :
    OrthonormalBasis (Fin 3) ℂ (EuclideanSpace ℂ (Fin 3)) :=
  Classical.choose (ic_schur_s03_apply_schur_thm A)

lemma ic_mat_s01_basis_exists (A : Matrix (Fin 3) (Fin 3) ℂ) :
    ∃ b : OrthonormalBasis (Fin 3) ℂ (EuclideanSpace ℂ (Fin 3)),
      (LinearMap.toMatrix b.toBasis b.toBasis (Matrix.toEuclideanLin A)).IsUpperTriangular := by
  exact ic_schur_s03_apply_schur_thm A


noncomputable def ic_mat_s02_def_basis (A : Matrix (Fin 3) (Fin 3) ℂ) :
    OrthonormalBasis (Fin 3) ℂ (EuclideanSpace ℂ (Fin 3)) :=
  Classical.choose (ic_mat_s01_basis_exists A)

noncomputable def ic_mat_s03_def_U (A : Matrix (Fin 3) (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  let b := ic_mat_s02_def_basis A
  fun i j => b j i

lemma ic_mat_s04_U_col (A : Matrix (Fin 3) (Fin 3) ℂ) (j : Fin 3) :
    let U := ic_mat_s03_def_U A
    let b := ic_mat_s02_def_basis A
    (fun i => U i j) = b j := by
  intro U b
  funext i
  simp [U, ic_mat_s03_def_U]
  aesop

lemma ic_mat_s05_orthonormal (A : Matrix (Fin 3) (Fin 3) ℂ) :
    let b := ic_mat_s02_def_basis A
    Orthonormal ℂ b := by
  exact (ic_mat_s02_def_basis A).orthonormal

lemma ic_mat_s06_inner_prod_calc (A : Matrix (Fin 3) (Fin 3) ℂ) (i j : Fin 3) :
    let U := ic_mat_s03_def_U A
    let col_i := fun k => U k i
    let col_j := fun k => U k j
    @inner ℂ _ _ (WithLp.toLp (p := 2) col_i) (WithLp.toLp (p := 2) col_j) = if i = j then 1 else 0 := by
  intro U col_i col_j
  simp [col_i, col_j]
  simp [U, ic_mat_s03_def_U]
  have h := (ic_mat_s02_def_basis A).orthonormal
  simp [Orthonormal] at h ⊢
  aesop

lemma ic_mat_s07_U_star_U (A : Matrix (Fin 3) (Fin 3) ℂ) (i j : Fin 3) :
    let U := ic_mat_s03_def_U A
    (U.conjTranspose * U) i j = if i = j then 1 else 0 := by
  intro U
  rw [Matrix.mul_apply]
  have h := ic_mat_s06_inner_prod_calc A i j
  simp [U, Matrix.conjTranspose, EuclideanSpace.inner_eq_star_dotProduct] at h ⊢
  simp [ mul_comm] at h ⊢
  exact h

lemma ic_mat_s08_U_unitary_left (A : Matrix (Fin 3) (Fin 3) ℂ) :
    let U := ic_mat_s03_def_U A
    U.conjTranspose * U = 1 := by
  intro U
  ext i j
  rw [ic_mat_s07_U_star_U A i j]
  rw [Matrix.one_apply]

lemma ic_mat_s09_U_unitary_right (A : Matrix (Fin 3) (Fin 3) ℂ) :
    let U := ic_mat_s03_def_U A
    U * U.conjTranspose = 1 := by
  intro U
  have h := ic_mat_s08_U_unitary_left A
  exact mul_eq_one_comm.mp h

lemma ic_mat_s10_lin_entry_def (A : Matrix (Fin 3) (Fin 3) ℂ) (i j : Fin 3) :
    let b := ic_mat_s02_def_basis A
    let T := Matrix.toEuclideanLin A
    (LinearMap.toMatrix b.toBasis b.toBasis T) i j = (b.toBasis.repr (T (b j))) i := by
  simp [LinearMap.toMatrix_apply]

lemma ic_mat_s11_lin_entry_eq_inner (A : Matrix (Fin 3) (Fin 3) ℂ) (i j : Fin 3) :
    let b := ic_mat_s02_def_basis A
    let T := Matrix.toEuclideanLin A
    (LinearMap.toMatrix b.toBasis b.toBasis T) i j = ⟪b i, T (b j)⟫ := by
  intro b T
  rw [ic_mat_s10_lin_entry_def A i j]
  rw [OrthonormalBasis.coe_toBasis_repr_apply]
  rw [OrthonormalBasis.repr_apply_apply]

lemma ic_mat_s12_01_assoc (A : Matrix (Fin 3) (Fin 3) ℂ) :
    let U := ic_mat_s03_def_U A
    U.conjTranspose * A * U = U.conjTranspose * (A * U) := by
  intro U
  exact Matrix.mul_assoc U.conjTranspose A U

lemma ic_mat_s12_02_mul_apply (X Y : Matrix (Fin 3) (Fin 3) ℂ) (i j : Fin 3) :
    (X * Y) i j = ∑ k, X i k * Y k j := by
  simp [Matrix.mul_apply]

lemma ic_mat_s12_03_expand_rhs (A : Matrix (Fin 3) (Fin 3) ℂ) (i j : Fin 3) :
    let U := ic_mat_s03_def_U A
    (U.conjTranspose * (A * U)) i j = ∑ k : Fin 3, (Matrix.conjTranspose U) i k * (A * U) k j := by
  intro U
  exact ic_mat_s12_02_mul_apply U.conjTranspose (A * U) i j

lemma ic_mat_s12_04_rewrite_lhs (A : Matrix (Fin 3) (Fin 3) ℂ) (i j : Fin 3) :
    let U := ic_mat_s03_def_U A
    (U.conjTranspose * A * U) i j = (U.conjTranspose * (A * U)) i j := by
  intro U
  rw [ic_mat_s12_01_assoc A]

lemma ic_mat_s12_mat_mul_expansion (A : Matrix (Fin 3) (Fin 3) ℂ) (i j : Fin 3) :
    let U := ic_mat_s03_def_U A
    (U.conjTranspose * A * U) i j = ∑ k : Fin 3, (Matrix.conjTranspose U) i k * (A * U) k j := by
  intro U
  rw [ic_mat_s12_04_rewrite_lhs A i j]
  rw [ic_mat_s12_03_expand_rhs A i j]

lemma ic_mat_s13_01_01_pi_def (u v : EuclideanSpace ℂ (Fin 3)) :
    ⟪u, v⟫ = ∑ k : Fin 3, ⟪u k, v k⟫ := by
  exact PiLp.inner_apply u v

lemma ic_mat_s13_01_02_complex_inner (a b : ℂ) :
    ⟪a, b⟫ = star a * b := by
  simp [Inner.inner]
  rw [mul_comm]

lemma ic_mat_s13_01_03_term_eq (u v : EuclideanSpace ℂ (Fin 3)) (k : Fin 3) :
    ⟪u k, v k⟫ = star (u k) * v k := by
  exact ic_mat_s13_01_02_complex_inner (u k) (v k)

lemma ic_mat_s13_01_04_sum_congr (u v : EuclideanSpace ℂ (Fin 3)) :
    ∑ k : Fin 3, ⟪u k, v k⟫ = ∑ k : Fin 3, star (u k) * v k := by
  apply Finset.sum_congr rfl
  intro k _
  exact ic_mat_s13_01_03_term_eq u v k

lemma ic_mat_s13_01_inner_sum (u v : EuclideanSpace ℂ (Fin 3)) :
    ⟪u, v⟫ = ∑ k : Fin 3, star (u k) * v k := by
  rw [ic_mat_s13_01_01_pi_def u v]
  rw [ic_mat_s13_01_04_sum_congr u v]

lemma ic_mat_s13_02_conj_entry (A : Matrix (Fin 3) (Fin 3) ℂ) (i k : Fin 3) :
    let U := ic_mat_s03_def_U A
    let b := ic_mat_s02_def_basis A
    (Matrix.conjTranspose U) i k = star ((b i) k) := by
  intro U b
  simp only [Matrix.conjTranspose, Matrix.transpose, star]
  simp [U, ic_mat_s03_def_U]
  aesop

lemma ic_mat_s13_03_action_entry (A : Matrix (Fin 3) (Fin 3) ℂ) (k j : Fin 3) :
    let U := ic_mat_s03_def_U A
    let b := ic_mat_s02_def_basis A
    (A * U) k j = ((Matrix.toEuclideanLin A) (b j)) k := by
  intro U b
  rw [matrix_toEuclideanLin_apply_coord]
  simp [U, ic_mat_s03_def_U, Matrix.mul_apply, Matrix.mulVec]
  ring_nf
  aesop

lemma ic_mat_s13_04_sum_eq (A : Matrix (Fin 3) (Fin 3) ℂ) (i j : Fin 3) :
    let U := ic_mat_s03_def_U A
    let b := ic_mat_s02_def_basis A
    ∑ k, (Matrix.conjTranspose U) i k * (A * U) k j = 
    ∑ k, star ((b i) k) * ((Matrix.toEuclideanLin A) (b j)) k := by
  intro U b
  apply Finset.sum_congr rfl
  intro k _
  rw [ic_mat_s13_02_conj_entry A i k]
  rw [ic_mat_s13_03_action_entry A k j]

lemma ic_mat_s13_mat_mul_eq_inner (A : Matrix (Fin 3) (Fin 3) ℂ) (i j : Fin 3) :
    let U := ic_mat_s03_def_U A
    let b := ic_mat_s02_def_basis A
    (U.conjTranspose * A * U) i j = ⟪b i, (Matrix.toEuclideanLin A) (b j)⟫ := by
  intro U b
  rw [ic_mat_s12_mat_mul_expansion A i j]
  rw [ic_mat_s13_04_sum_eq A i j]
  rw [ic_mat_s13_01_inner_sum (b i) ((Matrix.toEuclideanLin A) (b j))]

lemma ic_mat_s14_matrices_eq (A : Matrix (Fin 3) (Fin 3) ℂ) :
    let U := ic_mat_s03_def_U A
    let b := ic_mat_s02_def_basis A
    U.conjTranspose * A * U = LinearMap.toMatrix b.toBasis b.toBasis (Matrix.toEuclideanLin A) := by
  intro U b
  ext i j
  rw [ic_mat_s13_mat_mul_eq_inner A i j]
  rw [ic_mat_s11_lin_entry_eq_inner A i j]

lemma ic_mat_s15_upper_triangular (A : Matrix (Fin 3) (Fin 3) ℂ) :
    let U := ic_mat_s03_def_U A
    (U.conjTranspose * A * U).IsUpperTriangular := by
  intro U
  rw [ic_mat_s14_matrices_eq A]
  exact Classical.choose_spec (ic_mat_s01_basis_exists A)

lemma ic_B02_schur_exists (A : Matrix (Fin 3) (Fin 3) ℂ) :
    ∃ U : Matrix (Fin 3) (Fin 3) ℂ, 
      U * U.conjTranspose = 1 ∧ 
      (U.conjTranspose * A * U).IsUpperTriangular := by
  let U := ic_mat_s03_def_U A
  use U
  constructor
  · exact ic_mat_s09_U_unitary_right A
  · exact ic_mat_s15_upper_triangular A

lemma ic_B03_strict_upper (T : Matrix (Fin 3) (Fin 3) ℂ) 
    (h_upper : T.IsUpperTriangular) 
    (h_nil : T ^ 3 = 0) :
    T 0 0 = 0 ∧ T 1 1 = 0 ∧ T 2 2 = 0 := by
  have h10 : T 1 0 = 0 := h_upper 1 0 (by decide)
  have h20 : T 2 0 = 0 := h_upper 2 0 (by decide)
  have h21 : T 2 1 = 0 := h_upper 2 1 (by decide)
  have h00_cube : (T 0 0) ^ 3 = 0 := by
    have h := congrArg (fun M => M 0 0) h_nil
    have h00 : (T ^ 3) 0 0 = (T 0 0) ^ 3 := by
      calc
        (T ^ 3) 0 0 = (T ^ 2) 0 0 * T 0 0 := by
          simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three, h10, h20]
        _ = (T 0 0) ^ 2 * T 0 0 := by
          have h00' : (T ^ 2) 0 0 = (T 0 0) ^ 2 := by
            simp [pow_two, Matrix.mul_apply, Fin.sum_univ_three, h10, h20]
          simp [h00']
        _ = (T 0 0) ^ 3 := by ring
    simpa [h00] using h
  have h11_cube : (T 1 1) ^ 3 = 0 := by
    have h := congrArg (fun M => M 1 1) h_nil
    have h11 : (T ^ 3) 1 1 = (T 1 1) ^ 3 := by
      calc
        (T ^ 3) 1 1 = (T ^ 2) 1 1 * T 1 1 := by
          simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three, h10, h21]
          aesop
        _ = (T 1 1) ^ 2 * T 1 1 := by
          have h11' : (T ^ 2) 1 1 = (T 1 1) ^ 2 := by
            simp [pow_two, Matrix.mul_apply, Fin.sum_univ_three, h10, h21]
          simp [h11']
        _ = (T 1 1) ^ 3 := by ring
    simpa [h11] using h
  have h22_cube : (T 2 2) ^ 3 = 0 := by
    have h := congrArg (fun M => M 2 2) h_nil
    have h22 : (T ^ 3) 2 2 = (T 2 2) ^ 3 := by
      calc
        (T ^ 3) 2 2 = (T ^ 2) 2 2 * T 2 2 := by
          simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three, h20, h21]
        _ = (T 2 2) ^ 2 * T 2 2 := by
          have h22' : (T ^ 2) 2 2 = (T 2 2) ^ 2 := by
            simp [pow_two, Matrix.mul_apply, Fin.sum_univ_three, h20, h21]
          simp [h22']
        _ = (T 2 2) ^ 3 := by ring
    simpa [h22] using h
  refine ⟨?_, ?_, ?_⟩
  · exact eq_zero_of_pow_eq_zero h00_cube
  · exact eq_zero_of_pow_eq_zero h11_cube
  · exact eq_zero_of_pow_eq_zero h22_cube

lemma ic_B04_representation (T : Matrix (Fin 3) (Fin 3) ℂ)
    (h_upper : T.IsUpperTriangular)
    (h_diag : T 0 0 = 0 ∧ T 1 1 = 0 ∧ T 2 2 = 0) :
    T = UpperTri (T 0 1) (T 1 2) (T 0 2) := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals 
    try simp [UpperTri, h_diag]
    try aesop

lemma ic_B_reduction_to_triangular (A : Matrix (Fin 3) (Fin 3) ℂ) (h_nil : A ^ 3 = 0) :
    ∃ U : Matrix (Fin 3) (Fin 3) ℂ,
      U * U.conjTranspose = 1 ∧
      ∃ a b c : ℂ, U.conjTranspose * A * U = UpperTri a b c := by
  obtain ⟨U, hU_unitary, hU_upper⟩ : ∃ U : Matrix (Fin 3) (Fin 3) ℂ, U * U.conjTranspose = 1 ∧ ∃ T : Matrix (Fin 3) (Fin 3) ℂ, T.IsUpperTriangular ∧ U.conjTranspose * A * U = T := by
    have := ic_B02_schur_exists A;
    exact ⟨ this.choose, this.choose_spec.1, _, this.choose_spec.2, rfl ⟩;
  obtain ⟨T, hT_upper, hT_eq⟩ := hU_upper
  have hT_diag : T 0 0 = 0 ∧ T 1 1 = 0 ∧ T 2 2 = 0 := by
    have hT_nilpotent : T^3 = 0 := by
      have hT_nilpotent : T^3 = Uᴴ * A^3 * U := by
        simp +decide [ ← hT_eq, pow_succ, mul_assoc ];
        simp +decide [ ← mul_assoc, hU_unitary ];
      aesop;
    exact ic_B03_strict_upper T hT_upper hT_nilpotent;
  have hT_repr : T = UpperTri (T 0 1) (T 1 2) (T 0 2) :=
    ic_B04_representation T hT_upper hT_diag
  refine ⟨U, hU_unitary, T 0 1, T 1 2, T 0 2, ?_⟩
  calc
    U.conjTranspose * A * U = T := hT_eq
    _ = UpperTri (T 0 1) (T 1 2) (T 0 2) := hT_repr

lemma ic_C01_apply_T (a b c : ℂ) (x : E3) :
    UpperTri a b c *ᵥ x = ![a * x 1 + c * x 2, b * x 2, 0] := by
  rw [UpperTri]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

lemma ic_C02_apply_T_adj (a b c : ℂ) (x : E3) :
    (UpperTri a b c).conjTranspose *ᵥ x = ![0, star a * x 0, star c * x 0 + star b * x 1] := by
  rw [UpperTri]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.conjTranspose_apply]

lemma ic_C03_eq_comp1 (a b c : ℂ) (x : E3) (alpha beta : ℂ)
    (h_eq : (UpperTri a b c).conjTranspose *ᵥ x = alpha • x + beta • (UpperTri a b c *ᵥ x)) :
    star a * x 0 = alpha * x 1 + beta * (b * x 2) := by
  have h := congr_fun h_eq 1
  rw [ic_C01_apply_T, ic_C02_apply_T_adj] at h
  simp at h
  exact h

lemma ic_C04_eq_comp2 (a b c : ℂ) (x : E3) (alpha beta : ℂ)
    (h_eq : (UpperTri a b c).conjTranspose *ᵥ x = alpha • x + beta • (UpperTri a b c *ᵥ x)) :
    star c * x 0 + star b * x 1 = alpha * x 2 := by
  have h := congr_fun h_eq 2
  rw [ic_C01_apply_T, ic_C02_apply_T_adj] at h
  simp at h
  exact h

lemma ic_C05_01_lhs_at_2 (a b c : ℂ) (x : E3) :
    ((UpperTri a b c).conjTranspose *ᵥ x) 2 = star c * x 0 + star b * x 1 := by
  rw [ic_C02_apply_T_adj]
  simp

lemma ic_C05_02_rhs_inner_at_2 (a b c : ℂ) (x : E3) :
    (UpperTri a b c *ᵥ x) 2 = 0 := by
  rw [ic_C01_apply_T]
  simp

lemma ic_C05_03_rhs_beta_term_at_2 (a b c : ℂ) (x : E3) (beta : ℂ) :
    (beta • (UpperTri a b c *ᵥ x)) 2 = 0 := by
  simp [ic_C05_02_rhs_inner_at_2]

lemma ic_C05_04_rhs_alpha_term_at_2 (x : E3) (alpha : ℂ) :
    (alpha • x) 2 = alpha * x 2 := by
  simp

lemma ic_C05_05_rhs_total_at_2 (a b c : ℂ) (x : E3) (alpha beta : ℂ) :
    (alpha • x + beta • (UpperTri a b c *ᵥ x)) 2 = alpha * x 2 := by
  rw [Pi.add_apply]
  have h_alpha : (alpha • x.ofLp) 2 = alpha * x.ofLp 2 := rfl
  have h_beta : (beta • UpperTri a b c *ᵥ x.ofLp) 2 = 0 := by
    rw [Pi.smul_apply]
    have h_zero : (UpperTri a b c *ᵥ x.ofLp) 2 = 0 := by
      simp [Matrix.mulVec, UpperTri]
    rw [h_zero]
    simp
  rw [h_alpha, h_beta]
  aesop

lemma ic_C05_06_scalar_eq (a b c : ℂ) (x : E3) (alpha beta : ℂ)
    (h_eq : (UpperTri a b c).conjTranspose *ᵥ x = alpha • x + beta • (UpperTri a b c *ᵥ x)) :
    star c * x 0 + star b * x 1 = alpha * x 2 := by
  have h_at_2 := congr_fun h_eq 2
  rw [ic_C05_01_lhs_at_2] at h_at_2
  rw [ic_C05_05_rhs_total_at_2] at h_at_2
  exact h_at_2

lemma ic_C05_07_mult_x1 (a b c : ℂ) (x : E3) (alpha beta : ℂ)
    (h_eq : (UpperTri a b c).conjTranspose *ᵥ x = alpha • x + beta • (UpperTri a b c *ᵥ x)) :
    (star c * x 0 + star b * x 1) * x 1 = (alpha * x 2) * x 1 := by
  rw [ic_C05_06_scalar_eq a b c x alpha beta h_eq]

lemma ic_C05_08_commute_rhs (a b c : ℂ) (x : E3) (alpha beta : ℂ)
    (h_eq : (UpperTri a b c).conjTranspose *ᵥ x = alpha • x + beta • (UpperTri a b c *ᵥ x)) :
    (star c * x 0 + star b * x 1) * x 1 = alpha * x 1 * x 2 := by
  rw [ic_C05_07_mult_x1 a b c x alpha beta h_eq]
  ring

lemma ic_C05_09_symm (a b c : ℂ) (x : E3) (alpha beta : ℂ)
    (h_eq : (UpperTri a b c).conjTranspose *ᵥ x = alpha • x + beta • (UpperTri a b c *ᵥ x)) :
    alpha * x 1 * x 2 = (star c * x 0 + star b * x 1) * x 1 := by
  rw [ic_C05_08_commute_rhs a b c x alpha beta h_eq]

lemma ic_C05_alpha_x1_x2 (a b c : ℂ) (x : E3) (alpha beta : ℂ)
    (h_eq : (UpperTri a b c).conjTranspose *ᵥ x = alpha • x + beta • (UpperTri a b c *ᵥ x)) :
    alpha * x 1 * x 2 = (star c * x 0 + star b * x 1) * x 1 := by
  exact ic_C05_09_symm a b c x alpha beta h_eq

lemma ic_C06_star_a_x0_x2 (a b c : ℂ) (x : E3) (alpha beta : ℂ)
    (h_eq : (UpperTri a b c).conjTranspose *ᵥ x = alpha • x + beta • (UpperTri a b c *ᵥ x)) :
    star a * x 0 * x 2 = alpha * x 1 * x 2 + beta * b * (x 2)^2 := by
  have h := ic_C03_eq_comp1 a b c x alpha beta h_eq
  linear_combination x 2 * h

lemma ic_C_beta_relation (a b c : ℂ) (x : E3) (alpha beta : ℂ) (_hx2 : x 2 ≠ 0)
    (h_eq : (UpperTri a b c).conjTranspose *ᵥ x = alpha • x + beta • (UpperTri a b c *ᵥ x)) :
    star a * x 0 * x 2 = (star c * x 0 + star b * x 1) * x 1 + beta * b * (x 2)^2 := by
  have h1 := ic_C05_alpha_x1_x2 a b c x alpha beta h_eq
  have h2 := ic_C06_star_a_x0_x2 a b c x alpha beta h_eq
  rw [ic_C05_alpha_x1_x2 a b c x alpha beta h_eq] at h2
  exact h2

lemma ic_D01_01_test_vector : 
    let v : E3 := EuclideanSpace.single (0 : Fin 3) (1 : ℂ)
    v 0 = 1 ∧ v 1 = 0 ∧ v 2 = 0 := by
  intro v
  simp []
  aesop

lemma ic_D01_02_Tv_zero (a b c : ℂ) :
    let v : E3 := EuclideanSpace.single (0 : Fin 3) (1 : ℂ)
    UpperTri a b c *ᵥ v = 0 := by
  intro v
  rw [ic_C01_apply_T]
  simp [v]

lemma ic_D01_03_T_adj_v (a b c : ℂ) :
    let v : E3 := EuclideanSpace.single (0 : Fin 3) (1 : ℂ)
    (UpperTri a b c).conjTranspose *ᵥ v = ![0, star a, star c] := by
  intro v
  rw [ic_C02_apply_T_adj]
  simp [v]

lemma ic_D01_04_instantiate_crabb (a b c : ℂ) 
    (h_prop : HasCrabbProperty (UpperTri a b c)) :
    ∃ x : E3, ‖x‖ = 1 ∧ ∃ alpha beta : ℂ, 
      (UpperTri a b c).conjTranspose *ᵥ x = alpha • x + beta • (UpperTri a b c *ᵥ x) := by
  rcases h_prop with ⟨x, hx, sc, h_beta⟩
  refine ⟨x, hx, sc.alpha, sc.beta, ?_⟩
  have h1 : (adjoint (Matrix.toEuclideanLin (UpperTri a b c)) x).ofLp = (UpperTri a b c).conjTranspose *ᵥ x.ofLp := by
    have h_def : ∀ (w : E3), ⟪w, adjoint (Matrix.toEuclideanLin (UpperTri a b c)) x⟫ = ⟪Matrix.toEuclideanLin (UpperTri a b c) w, x⟫ := by
      intro w
      have h1 := adjoint_inner_left (Matrix.toEuclideanLin (UpperTri a b c)) w x
      have h2 : ⟪w, (adjoint (Matrix.toEuclideanLin (UpperTri a b c))) x⟫ = star ⟪(adjoint (Matrix.toEuclideanLin (UpperTri a b c))) x, w⟫ := by
        rw [← inner_conj_symm]
        all_goals try simp
      have h3 : star ⟪x, (toEuclideanLin (UpperTri a b c)) w⟫ = ⟪(toEuclideanLin (UpperTri a b c)) w, x⟫ := by
        rw [← inner_conj_symm]
        all_goals try simp
      rw [h2, h1, h3]
    funext i
    have h_at_i := h_def (EuclideanSpace.single i 1)
    simp only [EuclideanSpace.inner_eq_star_dotProduct, matrix_toEuclideanLin_apply, 
          Matrix.mulVec, Matrix.conjTranspose_apply] at h_at_i ⊢
    have h1 : ∀ v : E3, v.ofLp ⬝ᵥ star (EuclideanSpace.single i 1).ofLp = v.ofLp i := by
      intro v
      simp [dotProduct, Fin.sum_univ_three]
      fin_cases i <;>
      simp [Pi.single, mul_one, mul_zero, add_zero, zero_add]
    have h2 : x.ofLp ⬝ᵥ star (UpperTri a b c *ᵥ (EuclideanSpace.single i 1).ofLp) = 
            (fun j => star (UpperTri a b c j i)) ⬝ᵥ x.ofLp := by
      fin_cases i <;> 
      simp [dotProduct, Fin.sum_univ_three, UpperTri]
      ring
      ring
    rw [← h1 ((adjoint (Matrix.toEuclideanLin (UpperTri a b c))) x)]
    rw [h_at_i]
    rw [h2]
  rw [← h1]
  have h_eq : (adjoint (Matrix.toEuclideanLin (UpperTri a b c)) x).ofLp = 
      (sc.alpha • x + sc.beta • (Matrix.toEuclideanLin (UpperTri a b c) x)).ofLp := by
    rw [show adjoint (Matrix.toEuclideanLin (UpperTri a b c)) x = sc.alpha • x + sc.beta • (Matrix.toEuclideanLin (UpperTri a b c) x) by exact sc.h_decomp]
  have h_conv : (sc.alpha • x + sc.beta • (Matrix.toEuclideanLin (UpperTri a b c) x)).ofLp = 
      sc.alpha • x.ofLp + sc.beta • ((Matrix.toEuclideanLin (UpperTri a b c) x).ofLp) := by
    aesop
  have h_apply : (Matrix.toEuclideanLin (UpperTri a b c) x).ofLp = UpperTri a b c *ᵥ x.ofLp := by
    simp []
  rw [h_eq, h_conv, h_apply]

lemma ic_D01_05_simplify_eq (a b c : ℂ) (alpha beta : ℂ) :
    let v : E3 := EuclideanSpace.single (0 : Fin 3) (1 : ℂ)
    (UpperTri a b c).conjTranspose *ᵥ v = alpha • v + beta • (UpperTri a b c *ᵥ v) →
    (UpperTri a b c).conjTranspose *ᵥ v = alpha • v := by
  intro v h_eq
  rw [ic_D01_02_Tv_zero] at h_eq
  simp at h_eq
  exact h_eq

lemma ic_D01_06_vector_eq (a b c : ℂ) (alpha : ℂ) 
    (h_simple : (UpperTri a b c).conjTranspose *ᵥ ![1, 0, 0] = alpha • ![1, 0, 0]) :
    ![0, star a, star c] = ![alpha, 0, 0] := by
  let v : E3 := EuclideanSpace.single (0 : Fin 3) (1 : ℂ)
  have hv : v.ofLp = ![1, 0, 0] := by
    ext i
    fin_cases i <;> simp [v]
  have h_adj : (UpperTri a b c).conjTranspose *ᵥ v = ![0, star a, star c] := by
    have h := ic_C02_apply_T_adj a b c v
    dsimp [v] at h
    simp [] at h
    rw [hv]
    have h_col : (UpperTri a b c)ᴴ *ᵥ ![1, 0, 0] = (UpperTri a b c)ᴴ.col 0 := by
      ext i
      simp [Matrix.mulVec, Matrix.col]
      aesop
    rw [h_col]
    rw [h]
    simp [star]
    aesop
  have h_simple_v : (UpperTri a b c).conjTranspose *ᵥ v = alpha • v := by
    simpa [hv] using h_simple
  have h_vec : ![0, star a, star c] = alpha • v :=
    (h_adj.symm.trans h_simple_v)
  have h_alpha : alpha • v = ![alpha, 0, 0] := by
    ext i
    fin_cases i <;> simp [v, Pi.smul_apply]
  simpa [h_alpha] using h_vec

lemma ic_D01_07_alpha_val (a _b c : ℂ) (alpha : ℂ)
    (h_vec : ![0, star a, star c] = ![alpha, 0, 0]) :
    alpha = 0 := by
  have h := congr_fun h_vec 0
  simp at h
  symm
  exact h

lemma ic_D01_08_c_comp (a _b c : ℂ) (alpha : ℂ)
    (h_vec : ![0, star a, star c] = ![alpha, 0, 0]) :
    star c = 0 := by
  have h := congr_fun h_vec 2
  simp at h
  aesop

lemma ic_D01_09_solve_c (c : ℂ) (h : star c = 0) : c = 0 := by
  exact star_eq_zero.mp h

lemma ic_D01_c_eq_zero (a b c : ℂ)
    (h_prop : ∀ x : E3, ‖x‖ = 1 →
      ∃ (coeff : SpanCoeffs (UpperTri a b c) x), ‖coeff.beta‖ = 1) : c = 0 := by
  let v : E3 := EuclideanSpace.single (0 : Fin 3) (1 : ℂ)
  have hv_norm : ‖v‖ = 1 := by
    simp [v]
  rcases h_prop v hv_norm with ⟨coeff, _h_beta_norm⟩
  have h_eq :
      (UpperTri a b c).conjTranspose *ᵥ v.ofLp =
        coeff.alpha • v.ofLp + coeff.beta • (UpperTri a b c *ᵥ v.ofLp) := by
    have h_eq' :
        (Matrix.toEuclideanLin (UpperTri a b c)).adjoint v =
          coeff.alpha • v + coeff.beta • (Matrix.toEuclideanLin (UpperTri a b c) v) := by
      exact coeff.h_decomp
    rw [ic_A01_04_02_clm_adj (UpperTri a b c)] at h_eq'
    have h_eq'' := congrArg (fun y : E3 => y.ofLp) h_eq'
    simpa [matrix_toEuclideanLin_apply] using h_eq''
  have h_simple_v :
      (UpperTri a b c).conjTranspose *ᵥ v.ofLp = coeff.alpha • v.ofLp := by
    have h_zero : UpperTri a b c *ᵥ v.ofLp = 0 := by
      simpa [v] using (ic_D01_02_Tv_zero a b c)
    calc
      (UpperTri a b c).conjTranspose *ᵥ v.ofLp
          = coeff.alpha • v.ofLp + coeff.beta • (UpperTri a b c *ᵥ v.ofLp) := h_eq
      _ = coeff.alpha • v.ofLp + coeff.beta • 0 := by rw [h_zero]
      _ = coeff.alpha • v.ofLp := by simp
  have hv_vec : v.ofLp = ![1, 0, 0] := by
    ext i
    fin_cases i <;> simp [v]
  have h_simple :
      (UpperTri a b c).conjTranspose *ᵥ ![1, 0, 0] = coeff.alpha • ![1, 0, 0] := by
    simpa [hv_vec] using h_simple_v
  have h_vec : ![0, star a, star c] = ![coeff.alpha, 0, 0] := by
    exact ic_D01_06_vector_eq a b c coeff.alpha h_simple
  have h_star_c : star c = 0 := by
    exact ic_D01_08_c_comp a b c coeff.alpha h_vec
  exact ic_D01_09_solve_c c h_star_c

lemma ic_D02_01_apply_C (a b : ℂ) (x : E3) (beta : ℂ) (hx2 : x 2 ≠ 0)
    (h_eq : (UpperTri a b 0).conjTranspose *ᵥ x = 
            ((star b * x 1) / x 2) • x + beta • (UpperTri a b 0 *ᵥ x)) :
    star a * x 0 * x 2 = (star 0 * x 0 + star b * x 1) * x 1 + beta * b * (x 2)^2 := by
  let alpha := (star b * x 1) / x 2
  exact ic_C_beta_relation a b 0 x alpha beta hx2 h_eq

lemma ic_D02_02_simp_zero (a b : ℂ) (x : E3) (beta : ℂ) (hx2 : x 2 ≠ 0)
    (h_eq : (UpperTri a b 0).conjTranspose *ᵥ x = 
            ((star b * x 1) / x 2) • x + beta • (UpperTri a b 0 *ᵥ x)) :
    star a * x 0 * x 2 = star b * (x 1)^2 + beta * b * (x 2)^2 := by
  have h := ic_D02_01_apply_C a b x beta hx2 h_eq
  simp only [star_zero, zero_mul, zero_add] at h
  ring_nf at h ⊢
  exact h

lemma ic_D02_03_isolate (a b : ℂ) (x : E3) (beta : ℂ) (hx2 : x 2 ≠ 0)
    (h_eq : (UpperTri a b 0).conjTranspose *ᵥ x = 
            ((star b * x 1) / x 2) • x + beta • (UpperTri a b 0 *ᵥ x)) :
    beta * b * (x 2)^2 = star a * x 0 * x 2 - star b * (x 1)^2 := by
  have h := ic_D02_02_simp_zero a b x beta hx2 h_eq
  aesop

lemma ic_D02_04_denom_ne_zero (b : ℂ) (x : E3) (hb : b ≠ 0) (hx2 : x 2 ≠ 0) :
    b * (x 2)^2 ≠ 0 := by
  apply mul_ne_zero hb
  exact pow_ne_zero 2 hx2

lemma ic_D02_05_solve_linear (X Y Z : ℂ) (h_eq : X * Y = Z) (h_ne : Y ≠ 0) :
    X = Z / Y := by
  rw [←h_eq, mul_div_cancel_right₀ X h_ne]

lemma ic_D02_beta_rel_simple (a b : ℂ) (x : E3) (beta : ℂ) (hb : b ≠ 0) (hx2 : x 2 ≠ 0)
    (h_eq : (UpperTri a b 0).conjTranspose *ᵥ x = 
            ((star b * x 1) / x 2) • x + beta • (UpperTri a b 0 *ᵥ x)) :
    beta = (star a * x 0 * x 2 - star b * (x 1)^2) / (b * (x 2)^2) := by
  have h_iso := ic_D02_03_isolate a b x beta hx2 h_eq
  have h_denom := ic_D02_04_denom_ne_zero b x hb hx2
  have h_iso' : beta * (b * (x 2)^2) = star a * x 0 * x 2 - star b * (x 1)^2 := by
    rw [← mul_assoc]
    exact h_iso
  exact ic_D02_05_solve_linear beta (b * (x 2)^2) _ h_iso' h_denom

lemma ic_D03_01_comp_zero (a b : ℂ) (x : E3) (alpha beta : ℂ)
    (h_eq : (UpperTri a b 0).conjTranspose *ᵥ x = alpha • x + beta • (UpperTri a b 0 *ᵥ x)) :
    0 = alpha * x 0 + beta * a * x 1 := by
  have h := congr_fun h_eq 0
  rw [ic_C02_apply_T_adj, ic_C01_apply_T] at h
  simp only [Pi.add_apply, Pi.smul_apply, Matrix.cons_val_zero] at h
  have h_simplified : 0 = alpha * x.ofLp 0 + beta * a * x.ofLp 1 := by
    have h1 : alpha • x.ofLp 0 = alpha * x.ofLp 0 := by simp []
    have h2 : beta • (a * x.ofLp 1 + 0 * x.ofLp 2) = beta * a * x.ofLp 1 := by 
      simp []
      ring
    rw [h1, h2] at h
    exact h
  simpa using h_simplified

lemma ic_D03_02_alpha_val (a b : ℂ) (x : E3) (alpha beta : ℂ) (hx2 : x 2 ≠ 0)
    (h_eq : (UpperTri a b 0).conjTranspose *ᵥ x = alpha • x + beta • (UpperTri a b 0 *ᵥ x)) :
    alpha = (star b * x 1) / x 2 := by
  have h := congr_fun h_eq 2
  rw [ic_C02_apply_T_adj, ic_C01_apply_T] at h
  simp [Pi.add_apply, Pi.smul_apply] at h
  field_simp [hx2]
  aesop

lemma ic_D03_03_beta_alt (a b : ℂ) (x : E3) (beta : ℂ) 
    (ha : a ≠ 0) (hx1 : x 1 ≠ 0) (hx2 : x 2 ≠ 0)
    (h_comp0 : 0 = ((star b * x 1) / x 2) * x 0 + beta * a * x 1) :
    beta = - (star b * x 0) / (a * x 2) := by
  field_simp [hx2] at h_comp0
  have h1 : star b * x.ofLp 0 + x.ofLp 2 * beta * a = 0 := by
    apply (mul_left_inj' hx1).mp
    aesop
  have h2 : x.ofLp 2 * beta * a = - (star b * x.ofLp 0) := by
    calc
      x.ofLp 2 * beta * a = (star b * x.ofLp 0 + x.ofLp 2 * beta * a) - star b * x.ofLp 0 := by ring
      _ = - (star b * x.ofLp 0) := by rw [h1]; ring
  field_simp [ha, hx2]
  have : beta * (a * x.ofLp 2) = -(star b * x.ofLp 0) := by
    calc
      beta * (a * x.ofLp 2) = x.ofLp 2 * beta * a := by ring
      _ = -(star b * x.ofLp 0) := h2
  calc
    beta * a * x.ofLp 2 = beta * (a * x.ofLp 2) := by ring
    _ = -(star b * x.ofLp 0) := this

lemma ic_D03_04_poly_constraint (a b : ℂ) (x : E3) (beta : ℂ)
    (ha : a ≠ 0) (hb : b ≠ 0) (_hx1 : x 1 ≠ 0) (hx2 : x 2 ≠ 0)
    (h_beta1 : beta = (star a * x 0 * x 2 - star b * (x 1)^2) / (b * (x 2)^2))
    (h_beta2 : beta = - (star b * x 0) / (a * x 2)) :
    a * star b * (x 1)^2 = (star a * a + star b * b) * x 0 * x 2 := by
  rw [h_beta2] at h_beta1
  field_simp [ha, hb, hx2] at h_beta1
  have h_eq : a * star b * x.ofLp 1 ^ 2 = (star a * a + star b * b) * x.ofLp 0 * x.ofLp 2 := by
    have eq1 : a * star b * x.ofLp 1 ^ 2 = star a * a * x.ofLp 0 * x.ofLp 2 + b * star b * x.ofLp 0 * x.ofLp 2 := by
      have h := h_beta1
      calc
        a * star b * x.ofLp 1 ^ 2 = a * star b * x.ofLp 1 ^ 2 := by rfl
        _ = a * (x.ofLp 0 * x.ofLp 2 * star a) - (-(star b * x.ofLp 0 * x.ofLp 2 * b)) := by 
          rw [h]
          ring
        _ = a * star a * x.ofLp 0 * x.ofLp 2 + star b * b * x.ofLp 0 * x.ofLp 2 := by 
          ring_nf
        _ = star a * a * x.ofLp 0 * x.ofLp 2 + b * star b * x.ofLp 0 * x.ofLp 2 := by
          simp [mul_comm]
    rw [eq1]
    ring_nf
  exact h_eq

lemma ic_D03_norm_constraints (a b : ℂ)
    (h_prop : ∀ x : E3, ‖x‖ = 1 →
      ∃ (coeff : SpanCoeffs (UpperTri a b 0) x), ‖coeff.beta‖ = 1) :
    ‖a‖ = 0 ∧ ‖b‖ = 0 := by
  let e0 : E3 := EuclideanSpace.single (0 : Fin 3) (1 : ℂ)
  have he0_norm : ‖e0‖ = 1 := by
    simp [e0]
  rcases h_prop e0 he0_norm with ⟨coeff0, _hbeta0⟩
  have h_eq0 :
      (UpperTri a b 0).conjTranspose *ᵥ e0.ofLp =
        coeff0.alpha • e0.ofLp + coeff0.beta • (UpperTri a b 0 *ᵥ e0.ofLp) := by
    have h' :
        (Matrix.toEuclideanLin (UpperTri a b 0)).adjoint e0 =
          coeff0.alpha • e0 + coeff0.beta • (Matrix.toEuclideanLin (UpperTri a b 0) e0) := by
      exact coeff0.h_decomp
    rw [ic_A01_04_02_clm_adj (UpperTri a b 0)] at h'
    have h'' := congrArg (fun y : E3 => y.ofLp) h'
    simpa [matrix_toEuclideanLin_apply] using h''
  have ha0 : a = 0 := by
    have h_comp1 := congr_fun h_eq0 1
    simp [UpperTri, e0, Matrix.mulVec, dotProduct] at h_comp1
    exact h_comp1

  let e1 : E3 := EuclideanSpace.single (1 : Fin 3) (1 : ℂ)
  have he1_norm : ‖e1‖ = 1 := by
    simp [e1]
  rcases h_prop e1 he1_norm with ⟨coeff1, _hbeta1⟩
  have h_eq1 :
      (UpperTri a b 0).conjTranspose *ᵥ e1.ofLp =
        coeff1.alpha • e1.ofLp + coeff1.beta • (UpperTri a b 0 *ᵥ e1.ofLp) := by
    have h' :
        (Matrix.toEuclideanLin (UpperTri a b 0)).adjoint e1 =
          coeff1.alpha • e1 + coeff1.beta • (Matrix.toEuclideanLin (UpperTri a b 0) e1) := by
      exact coeff1.h_decomp
    rw [ic_A01_04_02_clm_adj (UpperTri a b 0)] at h'
    have h'' := congrArg (fun y : E3 => y.ofLp) h'
    simpa [matrix_toEuclideanLin_apply] using h''
  have hb0 : b = 0 := by
    have h_comp2 := congr_fun h_eq1 2
    simp [UpperTri, e1, Matrix.mulVec, dotProduct] at h_comp2
    exact h_comp2

  constructor <;> simp [ha0, hb0]

lemma ic_D_parameters (a b c : ℂ) 
    (h_prop : ∀ x : E3, ‖x‖ = 1 →
      ∃ (coeff : SpanCoeffs (UpperTri a b c) x), ‖coeff.beta‖ = 1) :
    c = 0 ∧ ‖a‖ = 0 ∧ ‖b‖ = 0 := by
  obtain rfl := ic_D01_c_eq_zero a b c h_prop
  have h := ic_D03_norm_constraints a b h_prop
  exact ⟨rfl, h.1, h.2⟩

noncomputable def PhaseDiag (a b : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  if _ha : a = 0 then 1 else
  if _hb : b = 0 then 1 else
  !![ (a / ‖a‖) * (b / ‖b‖), 0, 0;
      0, b / ‖b‖, 0;
      0, 0, 1 ]

lemma ic_E02_phase_unitary (a b : ℂ) :
    (PhaseDiag a b) * (PhaseDiag a b).conjTranspose = 1 := by
  by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> simp [ha, hb, PhaseDiag];
  have h_diag : (a / ‖a‖) * (starRingEnd ℂ (a / ‖a‖)) = 1 ∧ (b / ‖b‖) * (starRingEnd ℂ (b / ‖b‖)) = 1 := by
    simp +decide [ Complex.mul_conj, Complex.normSq_eq_norm_sq, div_mul_div_comm ];
    exact ⟨ by rw [ div_eq_iff ( mul_ne_zero ( Complex.ofReal_ne_zero.mpr <| norm_ne_zero_iff.mpr ha ) ( Complex.ofReal_ne_zero.mpr <| norm_ne_zero_iff.mpr ha ) ) ] ; ring, by rw [ div_eq_iff ( mul_ne_zero ( Complex.ofReal_ne_zero.mpr <| norm_ne_zero_iff.mpr hb ) ( Complex.ofReal_ne_zero.mpr <| norm_ne_zero_iff.mpr hb ) ) ] ; ring ⟩;
  ext i j ; fin_cases i <;> fin_cases j <;> norm_num [ Matrix.vecMul, Matrix.vecHead, Matrix.vecTail, h_diag ];
  · simp_all +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ];
    grind;
  · aesop;
  · rfl;
  · rfl;
  · aesop

lemma ic_E03_conjugation_result (a b : ℂ) (ha : ‖a‖ = Real.sqrt 2) (hb : ‖b‖ = Real.sqrt 2) :
    let P := PhaseDiag a b
    let T := UpperTri a b 0
    P.conjTranspose * T * P = UpperTri (Real.sqrt 2) (Real.sqrt 2) 0 := by
  unfold PhaseDiag UpperTri;
  by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> simp_all +decide [ div_eq_mul_inv ];
  · exact absurd ‹0 = Real.sqrt 2› ( by positivity );
  · grind;
  · exact absurd ‹0 = Real.sqrt 2› ( by positivity );
  · ext i j; simp [Matrix.mul_apply, Matrix.conjTranspose];
    fin_cases i <;> fin_cases j <;> norm_num [ Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail ] <;> ring_nf <;> norm_num [ ha, hb, Complex.ext_iff, sq ];
    · norm_cast; norm_num [ pow_three ] ; ring_nf ; norm_num [ ha, hb, Complex.normSq, Complex.norm_def ] ;
      norm_num [ Complex.normSq, Complex.norm_def ] at *;
      grind;
    · simp_all +decide [ Complex.normSq, Complex.norm_def ] ; ring_nf ; norm_num;
      rw [ Real.sqrt_inj ( by nlinarith ) ( by nlinarith ) ] at * ; nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ]

lemma ic_h_circ_unitary
    (A U : Matrix (Fin 3) (Fin 3) ℂ)
    (hU : U * U.conjTranspose = 1)
    (h_circ : ∀ x : E3, ‖x‖ = 1 →
      ∃ (coeff : SpanCoeffs A x), ‖coeff.beta‖ = 1) :
    ∀ x : E3, ‖x‖ = 1 →
      ∃ (coeff : SpanCoeffs (U.conjTranspose * A * U) x), ‖coeff.beta‖ = 1 := by
  intro y hy
  have hx : ‖(Matrix.toEuclideanLin U) y‖ = 1 := by
    exact ic_inv_d04_unit_map U hU y hy
  rcases h_circ ((Matrix.toEuclideanLin U) y) hx with ⟨cA, h_beta⟩
  let cB : SpanCoeffs (U.conjTranspose * A * U) y := ic_inv_d06_construct_B_coeffs U A hU y cA
  refine ⟨cB, ?_⟩
  have h_beta_eq : cB.beta = cA.beta := by
    dsimp [cB, ic_inv_d06_construct_B_coeffs, ic_inv_construct_s04_def_beta]
  rw [h_beta_eq]
  exact h_beta

lemma ic_h_upper_params_zero :
    ∀ a b c : ℂ,
      (∀ x : E3, ‖x‖ = 1 →
        ∃ (coeff : SpanCoeffs (UpperTri a b c) x), ‖coeff.beta‖ = 1) →
      c = 0 ∧ ‖a‖ = 0 ∧ ‖b‖ = 0 := by
  intro a b c h_prop
  have hc0 : c = 0 := ic_D01_c_eq_zero a b c h_prop
  obtain rfl := hc0
  have h_norm := ic_D03_norm_constraints a b h_prop
  exact ⟨rfl, h_norm.1, h_norm.2⟩

theorem constant_beta_implies_crabb_of_upper_params
    (A : Matrix (Fin 3) (Fin 3) ℂ)
    (h_nil : A ^ 3 = 0)
    (h_circ : ∀ x : E3, ‖x‖ = 1 →
      ∃ (coeff : SpanCoeffs A x), ‖coeff.beta‖ = 1)
    (h_upper_params :
      ∀ a b c : ℂ,
        (∀ x : E3, ‖x‖ = 1 →
          ∃ (coeff : SpanCoeffs (UpperTri a b c) x), ‖coeff.beta‖ = 1) →
        c = 0 ∧ ‖a‖ = Real.sqrt 2 ∧ ‖b‖ = Real.sqrt 2) :
    ∃ (U : Matrix (Fin 3) (Fin 3) ℂ),
      U * U.conjTranspose = 1 ∧
      let B := U.conjTranspose * A * U
      B 0 1 = Real.sqrt 2 ∧
      B 1 2 = Real.sqrt 2 ∧
      B 0 2 = 0 := by
  obtain ⟨U, hU_unitary, a, b, c, h_tri⟩ := ic_B_reduction_to_triangular A h_nil
  have h_circ_tri :
      ∀ x : E3, ‖x‖ = 1 →
        ∃ (coeff : SpanCoeffs (U.conjTranspose * A * U) x), ‖coeff.beta‖ = 1 := by
    exact ic_h_circ_unitary A U hU_unitary h_circ
  have h_prop_upper :
      ∀ x : E3, ‖x‖ = 1 →
        ∃ (coeff : SpanCoeffs (UpperTri a b c) x), ‖coeff.beta‖ = 1 := by
    have h_circ_tri' := h_circ_tri
    rw [h_tri] at h_circ_tri'
    intro x hx
    exact h_circ_tri' x hx
  have h_params : c = 0 ∧ ‖a‖ = Real.sqrt 2 ∧ ‖b‖ = Real.sqrt 2 :=
    h_upper_params a b c h_prop_upper
  have hc0 : c = 0 := h_params.1
  have ha : ‖a‖ = Real.sqrt 2 := h_params.2.1
  have hb : ‖b‖ = Real.sqrt 2 := h_params.2.2
  let P : Matrix (Fin 3) (Fin 3) ℂ := PhaseDiag a b
  have hP_unitary : P * P.conjTranspose = 1 := by
    simpa [P] using ic_E02_phase_unitary a b
  have h_phase :
      P.conjTranspose * UpperTri a b 0 * P = UpperTri (Real.sqrt 2) (Real.sqrt 2) 0 := by
    simpa [P] using ic_E03_conjugation_result a b ha hb
  let U' : Matrix (Fin 3) (Fin 3) ℂ := U * P
  refine ⟨U', ?_, ?_⟩
  · calc
      U' * U'.conjTranspose
          = (U * P) * (U * P).conjTranspose := by rfl
      _ = U * (P * P.conjTranspose) * U.conjTranspose := by
            simp [Matrix.mul_assoc]
      _ = U * U.conjTranspose := by simp [hP_unitary]
      _ = 1 := hU_unitary
  · dsimp [U']
    have hB :
        P.conjTranspose * U.conjTranspose * A * U * P =
          UpperTri (Real.sqrt 2) (Real.sqrt 2) 0 := by
      calc
        P.conjTranspose * U.conjTranspose * A * U * P
            = P.conjTranspose * (U.conjTranspose * A * U) * P := by
                simp [Matrix.mul_assoc]
        _ = P.conjTranspose * UpperTri a b c * P := by rw [h_tri]
        _ = P.conjTranspose * UpperTri a b 0 * P := by simp [hc0]
        _ = UpperTri (Real.sqrt 2) (Real.sqrt 2) 0 := h_phase
    have hB' :
        P.conjTranspose * U.conjTranspose * A * (U * P) =
          UpperTri (Real.sqrt 2) (Real.sqrt 2) 0 := by
      simpa [Matrix.mul_assoc] using hB
    have h01 : (P.conjTranspose * U.conjTranspose * A * (U * P)) 0 1 = Real.sqrt 2 := by
      exact congrArg (fun M => M 0 1) hB'
    have h12 : (P.conjTranspose * U.conjTranspose * A * (U * P)) 1 2 = Real.sqrt 2 := by
      exact congrArg (fun M => M 1 2) hB'
    have h02 : (P.conjTranspose * U.conjTranspose * A * (U * P)) 0 2 = 0 := by
      exact congrArg (fun M => M 0 2) hB'
    exact ⟨by simpa [UpperTri] using h01, by simpa [UpperTri] using h12, by simpa [UpperTri] using h02⟩

theorem constant_beta_implies_crabb
    (A : Matrix (Fin 3) (Fin 3) ℂ)
    (h_nil : A ^ 3 = 0)
    (h_circ : ∀ x : E3, ‖x‖ = 1 →
      ∃ (coeff : SpanCoeffs A x), ‖coeff.beta‖ = 1) :
    ∃ (U : Matrix (Fin 3) (Fin 3) ℂ),
      U * U.conjTranspose = 1 ∧
      let B := U.conjTranspose * A * U
      B 0 1 = 0 ∧
      B 1 2 = 0 ∧
      B 0 2 = 0 := by
  obtain ⟨U, hU_unitary, a, b, c, h_tri⟩ := ic_B_reduction_to_triangular A h_nil
  have h_circ_tri :
      ∀ x : E3, ‖x‖ = 1 →
        ∃ (coeff : SpanCoeffs (U.conjTranspose * A * U) x), ‖coeff.beta‖ = 1 := by
    exact ic_h_circ_unitary A U hU_unitary h_circ
  have h_prop_upper :
      ∀ x : E3, ‖x‖ = 1 →
        ∃ (coeff : SpanCoeffs (UpperTri a b c) x), ‖coeff.beta‖ = 1 := by
    have h_circ_tri' := h_circ_tri
    rw [h_tri] at h_circ_tri'
    exact h_circ_tri'
  have h_params : c = 0 ∧ ‖a‖ = 0 ∧ ‖b‖ = 0 :=
    ic_h_upper_params_zero a b c h_prop_upper
  have hc0 : c = 0 := h_params.1
  have ha0 : a = 0 := norm_eq_zero.mp h_params.2.1
  have hb0 : b = 0 := norm_eq_zero.mp h_params.2.2
  refine ⟨U, hU_unitary, ?_⟩
  dsimp
  rw [h_tri, ha0, hb0, hc0]
  simp [UpperTri]

theorem constant_beta_implies_zero_form
    (A : Matrix (Fin 3) (Fin 3) ℂ)
    (h_nil : A ^ 3 = 0)
    (h_circ : ∀ x : E3, ‖x‖ = 1 →
      ∃ (coeff : SpanCoeffs A x), ‖coeff.beta‖ = 1) :
    ∃ (U : Matrix (Fin 3) (Fin 3) ℂ),
      U * U.conjTranspose = 1 ∧
      let B := U.conjTranspose * A * U
      B 0 1 = 0 ∧
      B 1 2 = 0 ∧
      B 0 2 = 0 := by
  exact constant_beta_implies_crabb A h_nil h_circ

end InverseCrabb
