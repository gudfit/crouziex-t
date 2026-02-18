import MyProject.Basic
import MyProject.DegeneracyDense
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.MeasureTheory.Function.Jacobian

noncomputable section

open MeasureTheory
open MeasureTheory.Measure
open scoped Matrix.Norms.Elementwise

namespace MyProject

abbrev En (n : ℕ) := EuclideanSpace ℂ (Fin n)

noncomputable def matCLM {n : ℕ} (A : Mat n) : En n →L[ℂ] En n :=
  (Matrix.toEuclideanLin A).toContinuousLinearMap

noncomputable def numericalRangeMat {n : ℕ} (A : Mat n) : Set ℂ :=
  numericalRange (matCLM A)

def CondSC {n : ℕ} (SmoothBoundary : Mat n → Prop) (A : Mat n) : Prop :=
  SmoothBoundary A ∧ StrictConvex ℝ (numericalRangeMat A)

noncomputable def rotHermitian {n : ℕ} (A : Mat n) (θ : ℝ) : Mat n :=
  ((1 / 2 : ℂ) •
    ((Complex.exp (-(θ : ℂ) * Complex.I)) • A +
      (Complex.exp ((θ : ℂ) * Complex.I)) • A.conjTranspose))

def HasSimpleSpectrum {n : ℕ} (M : Mat n) : Prop :=
  Matrix.discr M ≠ 0

def CondS {n : ℕ} (ν : Measure ℝ) (A : Mat n) : Prop :=
  ∀ᵐ θ ∂ν, HasSimpleSpectrum (rotHermitian A θ)

lemma condSC_badset_null_of_components
    {n : ℕ}
    (μA : Measure (Mat n))
    (SmoothBoundary : Mat n → Prop)
    (hSmooth_bad : μA {A : Mat n | ¬ SmoothBoundary A} = 0)
    (hStrict_bad : μA {A : Mat n | ¬ StrictConvex ℝ (numericalRangeMat A)} = 0) :
    μA {A : Mat n | ¬ CondSC SmoothBoundary A} = 0 := by
  have hset :
      {A : Mat n | ¬ CondSC SmoothBoundary A}
        = ({A : Mat n | ¬ SmoothBoundary A} ∪
            {A : Mat n | ¬ StrictConvex ℝ (numericalRangeMat A)}) := by
    ext A
    constructor
    · intro hA
      by_cases hSmooth : SmoothBoundary A
      · right
        intro hStrict
        exact hA ⟨hSmooth, hStrict⟩
      · exact Or.inl hSmooth
    · intro hA
      intro hBoth
      rcases hA with hSmooth | hStrict
      · exact hSmooth hBoth.1
      · exact hStrict hBoth.2
  rw [hset]
  exact measure_union_null hSmooth_bad hStrict_bad

lemma badset_null_of_pointwise_null
    {n : ℕ}
    (μA : Measure (Mat n)) (ν : Measure ℝ)
    [SFinite μA] [SFinite ν]
    (Q : Mat n → ℝ → Prop)
    (hMeasBad : MeasurableSet {p : ℝ × Mat n | ¬ Q p.2 p.1})
    (hθ : ∀ θ : ℝ, μA {A : Mat n | ¬ Q A θ} = 0) :
    μA {A : Mat n | ¬ (∀ᵐ θ ∂ν, Q A θ)} = 0 := by
  let s : Set (ℝ × Mat n) := {p : ℝ × Mat n | ¬ Q p.2 p.1}
  have hs_meas : MeasurableSet s := hMeasBad
  have hs_ae_null : (fun θ => μA (Prod.mk θ ⁻¹' s)) =ᵐ[ν] 0 := by
    refine Filter.Eventually.of_forall ?_
    intro θ
    simpa [s] using hθ θ
  have hprod_zero : (ν.prod μA) s = 0 :=
    measure_prod_null_of_ae_null (μ := ν) (ν := μA) hs_meas hs_ae_null
  have hprod_ae : ∀ᵐ p ∂ ν.prod μA, Q p.2 p.1 := by
    rw [ae_iff]
    simpa [s] using hprod_zero
  have hθA : ∀ᵐ θ ∂ ν, ∀ᵐ A ∂ μA, Q A θ :=
    ae_ae_of_ae_prod hprod_ae
  have hMeasGood : MeasurableSet {p : ℝ × Mat n | Q p.2 p.1} := by
    simpa [s, Set.compl_setOf] using hs_meas.compl
  have hAθ : ∀ᵐ A ∂ μA, ∀ᵐ θ ∂ ν, Q A θ :=
    (ae_ae_comm (μ := ν) (ν := μA) (p := fun θ A => Q A θ) hMeasGood).1 hθA
  rw [ae_iff] at hAθ
  simpa using hAθ

lemma condS_badset_null_of_pointwise_null
    {n : ℕ}
    (μA : Measure (Mat n)) (ν : Measure ℝ)
    [SFinite μA] [SFinite ν]
    (hMeasBad : MeasurableSet {p : ℝ × Mat n | ¬ HasSimpleSpectrum (rotHermitian p.2 p.1)})
    (hθ : ∀ θ : ℝ, μA {A : Mat n | ¬ HasSimpleSpectrum (rotHermitian A θ)} = 0) :
    μA {A : Mat n | ¬ CondS ν A} = 0 := by
  simpa [CondS] using
    badset_null_of_pointwise_null (μA := μA) (ν := ν)
      (Q := fun A θ => HasSimpleSpectrum (rotHermitian A θ))
      hMeasBad hθ

theorem lem_degen_cTex_n_ge_two
    (n : ℕ) (hn : 2 ≤ n)
    (μA : Measure (Mat n)) [Measure.IsOpenPosMeasure μA] [SFinite μA]
    (ν : Measure ℝ) [SFinite ν]
    (SmoothBoundary : Mat n → Prop)
    (hSC_bad : μA {A : Mat n | ¬ CondSC SmoothBoundary A} = 0)
    (hS_measBad : MeasurableSet {p : ℝ × Mat n | ¬ HasSimpleSpectrum (rotHermitian p.2 p.1)})
    (hS_pointwise : ∀ θ : ℝ, μA {A : Mat n | ¬ HasSimpleSpectrum (rotHermitian A θ)} = 0) :
    Dense {A : Mat n | CondSC SmoothBoundary A ∧ CondS ν A} := by
  have hS_bad : μA {A : Mat n | ¬ CondS ν A} = 0 :=
    condS_badset_null_of_pointwise_null (μA := μA) (ν := ν) hS_measBad hS_pointwise
  exact lem_degen_n_ge_two n hn μA (CondSC SmoothBoundary) (CondS ν) hSC_bad hS_bad

lemma measurableSet_bad_rotHermitian_of_measurable_discr
    {n : ℕ}
    (hdiscr : Measurable (fun M : Mat n => Matrix.discr M)) :
    MeasurableSet {p : ℝ × Mat n | ¬ HasSimpleSpectrum (rotHermitian p.2 p.1)} := by
  have hrot : Continuous (fun p : ℝ × Mat n => rotHermitian p.2 p.1) := by
    unfold rotHermitian
    fun_prop
  simpa [HasSimpleSpectrum] using
    (measurableSet_eq_fun (hdiscr.comp hrot.measurable) measurable_const)

theorem lem_degen_cTex_n_ge_two_stronger
    (n : ℕ) (hn : 2 ≤ n)
    (μA : Measure (Mat n)) [Measure.IsOpenPosMeasure μA] [SFinite μA]
    (ν : Measure ℝ) [SFinite ν]
    (SmoothBoundary : Mat n → Prop)
    (hSmooth_bad : μA {A : Mat n | ¬ SmoothBoundary A} = 0)
    (hStrict_bad : μA {A : Mat n | ¬ StrictConvex ℝ (numericalRangeMat A)} = 0)
    (hdiscr : Measurable (fun M : Mat n => Matrix.discr M))
    (hS_pointwise : ∀ θ : ℝ, μA {A : Mat n | ¬ HasSimpleSpectrum (rotHermitian A θ)} = 0) :
    Dense {A : Mat n | CondSC SmoothBoundary A ∧ CondS ν A} := by
  have hSC_bad : μA {A : Mat n | ¬ CondSC SmoothBoundary A} = 0 :=
    condSC_badset_null_of_components (μA := μA) SmoothBoundary hSmooth_bad hStrict_bad
  have hS_measBad : MeasurableSet {p : ℝ × Mat n | ¬ HasSimpleSpectrum (rotHermitian p.2 p.1)} :=
    measurableSet_bad_rotHermitian_of_measurable_discr (n := n) hdiscr
  exact lem_degen_cTex_n_ge_two n hn μA ν SmoothBoundary hSC_bad hS_measBad hS_pointwise

/-!
Status of the remaining concrete paper subgoals:

* `(2)` is established below for `n = 2`.
* `(1)` and `(3)` are not true at full generality (without extra hypotheses on
  `SmoothBoundary` / the matrix measure), and we record explicit counterexamples.
-/

abbrev Mat2 := Mat 2

lemma continuous_discr_mat2 : Continuous (fun M : Mat2 => Matrix.discr M) := by
  have hEq : (fun M : Mat2 => Matrix.discr M)
      = fun M : Mat2 => Matrix.trace M ^ 2 - 4 * Matrix.det M := by
    funext M
    simpa using (Matrix.discr_fin_two (A := M))
  rw [hEq]
  exact (continuous_id.matrix_trace.pow 2).sub (continuous_const.mul continuous_id.matrix_det)

lemma continuous_rotHermitian_pair_mat2 :
    Continuous (fun p : ℝ × Mat2 => rotHermitian p.2 p.1) := by
  unfold rotHermitian
  fun_prop

theorem hS_measurable_badset_n2 :
    MeasurableSet {p : ℝ × Mat2 | ¬ HasSimpleSpectrum (rotHermitian p.2 p.1)} := by
  simpa [HasSimpleSpectrum] using (measurableSet_eq_fun
    ((continuous_discr_mat2.comp continuous_rotHermitian_pair_mat2).measurable)
    measurable_const)

theorem lem_degen_cTex_n2_stronger
    (μA : Measure Mat2) [Measure.IsOpenPosMeasure μA] [SFinite μA]
    (ν : Measure ℝ) [SFinite ν]
    (SmoothBoundary : Mat2 → Prop)
    (hSmooth_bad : μA {A : Mat2 | ¬ SmoothBoundary A} = 0)
    (hStrict_bad : μA {A : Mat2 | ¬ StrictConvex ℝ (numericalRangeMat A)} = 0)
    (hS_pointwise : ∀ θ : ℝ, μA {A : Mat2 | ¬ HasSimpleSpectrum (rotHermitian A θ)} = 0) :
    Dense {A : Mat2 | CondSC SmoothBoundary A ∧ CondS ν A} := by
  have hdiscr : Measurable (fun M : Mat2 => Matrix.discr M) :=
    continuous_discr_mat2.measurable
  exact lem_degen_cTex_n_ge_two_stronger 2 (by decide) μA ν SmoothBoundary
    hSmooth_bad hStrict_bad hdiscr hS_pointwise

lemma isHermitian_eq_zero_of_sq_eq_zero_mat2
    (M : Mat2) (hM : M.IsHermitian) (hM2 : M ^ 2 = 0) :
    M = 0 := by
  by_contra hne
  obtain ⟨v, t, ht_ne, hv_ne, hMv⟩ := Matrix.IsHermitian.exists_eigenvector_of_ne_zero hM hne
  have hpowv : (M ^ 2).mulVec v = (t * t) • v := by
    calc
      (M ^ 2).mulVec v = M.mulVec (M.mulVec v) := by
        simp [pow_two, Matrix.mulVec_mulVec]
      _ = M.mulVec (t • v) := by simp [hMv]
      _ = t • (M.mulVec v) := by simp [Matrix.mulVec_smul]
      _ = t • (t • v) := by simp [hMv]
      _ = (t * t) • v := by simp [mul_smul]
  have hzero : (M ^ 2).mulVec v = 0 := by simpa [hM2]
  have htsq_smul_zero : (t * t) • v = 0 := by simpa [hpowv] using hzero
  have htsq_zero : t * t = 0 := by
    exact (smul_eq_zero.mp htsq_smul_zero).resolve_right hv_ne
  have ht_zero : t = 0 := mul_eq_zero.mp htsq_zero |>.elim id id
  exact ht_ne ht_zero

lemma trace_star_of_isHermitian_mat2 (M : Mat2) (hM : M.IsHermitian) : star M.trace = M.trace := by
  calc
    star M.trace = (M.conjTranspose).trace := by
      simpa [Matrix.trace_conjTranspose] using (Matrix.trace_conjTranspose M).symm
    _ = M.trace := by simpa [hM.eq]

lemma isHermitian_scalar_of_star_eq_mat2 (a : ℂ) (ha : star a = a) :
    (Matrix.scalar (Fin 2) a : Mat2).IsHermitian := by
  unfold Matrix.IsHermitian
  ext i j
  by_cases h : i = j
  · subst h
    simp [Matrix.scalar_apply, ha]
  · have hji : j ≠ i := by exact fun hji => h hji.symm
    simp [Matrix.scalar_apply, h, hji]

lemma isHermitian_mem_range_scalar_of_discr_eq_zero_mat2
    (M : Mat2)
    (hM : M.IsHermitian)
    (hdiscr : Matrix.discr M = 0) :
    M ∈ Set.range (Matrix.scalar (Fin 2) : ℂ → Mat2) := by
  have htrace_star : star M.trace = M.trace := trace_star_of_isHermitian_mat2 M hM
  have hscalarHerm : (Matrix.scalar (Fin 2) (M.trace / 2) : Mat2).IsHermitian := by
    apply isHermitian_scalar_of_star_eq_mat2
    calc
      star (M.trace / 2) = star M.trace / star (2 : ℂ) := by
        simpa using (map_div₀ (starRingEnd ℂ) M.trace (2 : ℂ))
      _ = M.trace / (2 : ℂ) := by simpa [htrace_star]
  have hsubHerm : (M - Matrix.scalar (Fin 2) (M.trace / 2)).IsHermitian :=
    hM.sub hscalarHerm
  have hsq : (M - Matrix.scalar (Fin 2) (M.trace / 2)) ^ 2 = 0 := by
    calc
      (M - Matrix.scalar (Fin 2) (M.trace / 2)) ^ 2
          = Matrix.scalar (Fin 2) (M.discr / 4) := by
            simpa using (Matrix.sub_scalar_sq_eq_discr (m := M))
      _ = 0 := by simp [hdiscr]
  have hsub_zero : M - Matrix.scalar (Fin 2) (M.trace / 2) = 0 :=
    isHermitian_eq_zero_of_sq_eq_zero_mat2
      (M := M - Matrix.scalar (Fin 2) (M.trace / 2)) hsubHerm hsq
  refine ⟨M.trace / 2, ?_⟩
  exact (sub_eq_zero.mp hsub_zero).symm

lemma rotHermitian_isHermitian_mat2 (A : Mat2) (θ : ℝ) : (rotHermitian A θ).IsHermitian := by
  unfold rotHermitian
  refine Matrix.IsHermitian.ext ?_
  intro i j
  have hconj1 :
      (starRingEnd ℂ) (Complex.exp (-((θ : ℂ) * Complex.I)))
        = Complex.exp ((θ : ℂ) * Complex.I) := by
    calc
      (starRingEnd ℂ) (Complex.exp (-((θ : ℂ) * Complex.I)))
          = Complex.exp ((starRingEnd ℂ) (-((θ : ℂ) * Complex.I))) := by
            simpa [Complex.exp_conj] using
              (Complex.exp_conj (x := -((θ : ℂ) * Complex.I))).symm
      _ = Complex.exp ((θ : ℂ) * Complex.I) := by
        simp [mul_comm]
  have hconj2 :
      (starRingEnd ℂ) (Complex.exp ((θ : ℂ) * Complex.I))
        = Complex.exp (-((θ : ℂ) * Complex.I)) := by
    calc
      (starRingEnd ℂ) (Complex.exp ((θ : ℂ) * Complex.I))
          = Complex.exp ((starRingEnd ℂ) ((θ : ℂ) * Complex.I)) := by
            simpa [Complex.exp_conj] using
              (Complex.exp_conj (x := ((θ : ℂ) * Complex.I))).symm
      _ = Complex.exp (-((θ : ℂ) * Complex.I)) := by
        simp [mul_comm]
  simp
  rw [hconj1, hconj2]
  ring_nf

lemma rotHermitian_add_mat2 (A B : Mat2) (θ : ℝ) :
    rotHermitian (A + B) θ = rotHermitian A θ + rotHermitian B θ := by
  unfold rotHermitian
  simp [smul_add, add_assoc, add_left_comm]

lemma rotHermitian_real_smul_mat2 (r : ℝ) (A : Mat2) (θ : ℝ) :
    rotHermitian (r • A) θ = r • rotHermitian A θ := by
  unfold rotHermitian
  ext i j
  simp [smul_add, mul_comm, mul_left_comm, mul_assoc]
  ring_nf

def scalarSubmoduleMat2 : Submodule ℝ Mat2 where
  carrier := Set.range (Matrix.scalar (Fin 2) : ℂ → Mat2)
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    intro A B hA hB
    rcases hA with ⟨a, rfl⟩
    rcases hB with ⟨b, rfl⟩
    refine ⟨a + b, ?_⟩
    simpa using ((Matrix.scalar (Fin 2)).map_add a b)
  smul_mem' := by
    intro r A hA
    rcases hA with ⟨a, rfl⟩
    refine ⟨(r : ℂ) * a, ?_⟩
    ext i j
    by_cases h : i = j
    · subst h
      simp [Matrix.scalar_apply, mul_comm, mul_assoc]
    · have hji : j ≠ i := by exact fun hji => h hji.symm
      simp [Matrix.scalar_apply, h, hji]

def badRotSubmoduleMat2 (θ : ℝ) : Submodule ℝ Mat2 where
  carrier := {A : Mat2 | rotHermitian A θ ∈ scalarSubmoduleMat2}
  zero_mem' := by
    change rotHermitian (0 : Mat2) θ ∈ scalarSubmoduleMat2
    simp [scalarSubmoduleMat2, rotHermitian]
  add_mem' := by
    intro A B hA hB
    change rotHermitian (A + B) θ ∈ scalarSubmoduleMat2
    rw [rotHermitian_add_mat2]
    exact scalarSubmoduleMat2.add_mem hA hB
  smul_mem' := by
    intro r A hA
    change rotHermitian (r • A) θ ∈ scalarSubmoduleMat2
    rw [rotHermitian_real_smul_mat2]
    exact scalarSubmoduleMat2.smul_mem r hA

lemma diagonalWitness_not_mem_scalarSubmoduleMat2 :
    (!![(1 : ℂ), 0; 0, 0] : Mat2) ∉ scalarSubmoduleMat2 := by
  intro h
  rcases h with ⟨z, hz⟩
  have hz00 : z = (1 : ℂ) := by
    simpa [Matrix.scalar_apply] using congrArg (fun M : Mat2 => M 0 0) hz
  have hz11 : z = 0 := by
    simpa [Matrix.scalar_apply] using congrArg (fun M : Mat2 => M 1 1) hz
  have : (1 : ℂ) = 0 := by
    calc
      (1 : ℂ) = z := hz00.symm
      _ = 0 := hz11
  exact one_ne_zero this

lemma rotHermitian_scaled_diagonalWitness (θ : ℝ) :
    rotHermitian ((Complex.exp ((θ : ℂ) * Complex.I)) • (!![(1 : ℂ), 0; 0, 0] : Mat2)) θ
      = (!![(1 : ℂ), 0; 0, 0] : Mat2) := by
  ext i j
  fin_cases i <;> fin_cases j
  · have hprod1 : Complex.exp (-((θ : ℂ) * Complex.I)) * Complex.exp ((θ : ℂ) * Complex.I) = 1 := by
      calc
        Complex.exp (-((θ : ℂ) * Complex.I)) * Complex.exp ((θ : ℂ) * Complex.I)
            = Complex.exp ((-((θ : ℂ) * Complex.I)) + ((θ : ℂ) * Complex.I)) := by
              simpa using
                (Complex.exp_add (-((θ : ℂ) * Complex.I)) ((θ : ℂ) * Complex.I)).symm
        _ = 1 := by simp
    have hconj :
        (starRingEnd ℂ) (Complex.exp ((θ : ℂ) * Complex.I))
          = Complex.exp (-((θ : ℂ) * Complex.I)) := by
      calc
        (starRingEnd ℂ) (Complex.exp ((θ : ℂ) * Complex.I))
            = Complex.exp ((starRingEnd ℂ) ((θ : ℂ) * Complex.I)) := by
              simpa [Complex.exp_conj] using
                (Complex.exp_conj (x := ((θ : ℂ) * Complex.I))).symm
        _ = Complex.exp (-((θ : ℂ) * Complex.I)) := by simp [mul_comm]
    have hprod2 :
        Complex.exp ((θ : ℂ) * Complex.I) *
          (starRingEnd ℂ) (Complex.exp ((θ : ℂ) * Complex.I)) = 1 := by
      rw [hconj]
      simpa [mul_comm] using hprod1
    simp [rotHermitian, hprod1, hprod2]
    norm_num
  · simp [rotHermitian]
  · simp [rotHermitian]
  · simp [rotHermitian]

lemma badRotSubmoduleMat2_ne_top (θ : ℝ) : badRotSubmoduleMat2 θ ≠ ⊤ := by
  let Aθ : Mat2 := (Complex.exp ((θ : ℂ) * Complex.I)) • (!![(1 : ℂ), 0; 0, 0] : Mat2)
  have hAθ_not_mem : Aθ ∉ badRotSubmoduleMat2 θ := by
    intro hmem
    have hrot_mem : rotHermitian Aθ θ ∈ scalarSubmoduleMat2 := hmem
    have hrot_eq : rotHermitian Aθ θ = (!![(1 : ℂ), 0; 0, 0] : Mat2) := by
      simpa [Aθ] using rotHermitian_scaled_diagonalWitness θ
    exact diagonalWitness_not_mem_scalarSubmoduleMat2 (hrot_eq ▸ hrot_mem)
  intro htop
  have : Aθ ∈ badRotSubmoduleMat2 θ := by simpa [htop]
  exact hAθ_not_mem this

lemma badset_subset_badRotSubmoduleMat2 (θ : ℝ) :
    {A : Mat2 | ¬ HasSimpleSpectrum (rotHermitian A θ)} ⊆ badRotSubmoduleMat2 θ := by
  intro A hA
  have hdiscr_zero : Matrix.discr (rotHermitian A θ) = 0 := by
    simpa [HasSimpleSpectrum] using hA
  have hHerm : (rotHermitian A θ).IsHermitian := rotHermitian_isHermitian_mat2 A θ
  exact isHermitian_mem_range_scalar_of_discr_eq_zero_mat2
    (M := rotHermitian A θ) hHerm hdiscr_zero

theorem hS_pointwise_null_addHaar_n2
    (μA : Measure Mat2) [IsAddHaarMeasure μA]
    (θ : ℝ) :
    μA {A : Mat2 | ¬ HasSimpleSpectrum (rotHermitian A θ)} = 0 := by
  have hsub_zero : μA (badRotSubmoduleMat2 θ : Set Mat2) = 0 :=
    Measure.addHaar_submodule μA (badRotSubmoduleMat2 θ) (badRotSubmoduleMat2_ne_top θ)
  have hsubset :
      {A : Mat2 | ¬ HasSimpleSpectrum (rotHermitian A θ)} ⊆ (badRotSubmoduleMat2 θ : Set Mat2) :=
    badset_subset_badRotSubmoduleMat2 θ
  refine le_antisymm ?_ (zero_le _)
  exact (measure_mono hsubset).trans hsub_zero.le

def SmoothBoundarySimpleAtZero_n2 (A : Mat2) : Prop :=
  HasSimpleSpectrum (rotHermitian A 0)

theorem smoothBoundarySimpleAtZero_badset_null_addHaar_n2
    (μA : Measure Mat2) [IsAddHaarMeasure μA] :
    μA {A : Mat2 | ¬ SmoothBoundarySimpleAtZero_n2 A} = 0 := by
  simpa [SmoothBoundarySimpleAtZero_n2] using hS_pointwise_null_addHaar_n2 (μA := μA) (θ := 0)

def strictConvexBadParamSlice_n2 : Set Mat2 :=
  {A : Mat2 | A 0 1 = 0 ∧ A 0 0 ≠ A 1 1}

def strictConvexBadTargetB_n2 (A : Mat2) : ℂ :=
  (star (A 1 0)) * ((A 1 1 - A 0 0) * (star (A 1 1 - A 0 0))⁻¹)

def strictConvexBadE01_n2 : Mat2 :=
  Matrix.single 0 1 (1 : ℂ)

def strictConvexBadParamMap_n2 (A : Mat2) : Mat2 :=
  A + (strictConvexBadTargetB_n2 A - A 0 1) • strictConvexBadE01_n2

lemma differentiableAt_strictConvexBadTargetB_n2
    (A : Mat2) (hδ : A 1 1 - A 0 0 ≠ 0) :
    DifferentiableAt ℝ strictConvexBadTargetB_n2 A := by
  unfold strictConvexBadTargetB_n2
  have hstarδ : star (A 1 1 - A 0 0) ≠ 0 := star_ne_zero.mpr hδ
  fun_prop (disch := assumption)

lemma differentiableOn_strictConvexBadParamMap_n2 :
    DifferentiableOn ℝ strictConvexBadParamMap_n2 strictConvexBadParamSlice_n2 := by
  intro A hA
  have hδ : A 1 1 - A 0 0 ≠ 0 := by
    intro hzero
    apply hA.2
    have : A 1 1 = A 0 0 := sub_eq_zero.mp hzero
    simpa [eq_comm] using this
  have htarget : DifferentiableAt ℝ strictConvexBadTargetB_n2 A :=
    differentiableAt_strictConvexBadTargetB_n2 A hδ
  have hA01 : DifferentiableAt ℝ (fun B : Mat2 => B 0 1) A := by
    fun_prop
  have hscalar : DifferentiableAt ℝ
      (fun B : Mat2 => strictConvexBadTargetB_n2 B - B 0 1) A :=
    htarget.sub hA01
  have hsmul : DifferentiableAt ℝ
      (fun B : Mat2 =>
        (strictConvexBadTargetB_n2 B - B 0 1) • strictConvexBadE01_n2) A :=
    hscalar.smul (differentiableAt_const (c := strictConvexBadE01_n2))
  have hsum : DifferentiableAt ℝ
      (fun B : Mat2 => B +
        (strictConvexBadTargetB_n2 B - B 0 1) • strictConvexBadE01_n2) A :=
    differentiableAt_id.add hsmul
  simpa [strictConvexBadParamMap_n2] using hsum.differentiableWithinAt

def entry01ZeroSubmodule_n2 : Submodule ℝ Mat2 where
  carrier := {A : Mat2 | A 0 1 = 0}
  zero_mem' := by simp
  add_mem' := by
    intro A B hA hB
    have hA' : A 0 1 = 0 := hA
    have hB' : B 0 1 = 0 := hB
    change (A + B) 0 1 = 0
    simp [hA', hB']
  smul_mem' := by
    intro r A hA
    have hA' : A 0 1 = 0 := hA
    change (r • A) 0 1 = 0
    simp [hA']

lemma entry01ZeroSubmodule_n2_ne_top :
    entry01ZeroSubmodule_n2 ≠ (⊤ : Submodule ℝ Mat2) := by
  intro htop
  have hmem : (!![(0 : ℂ), 1; 0, 0] : Mat2) ∈ entry01ZeroSubmodule_n2 := by
    simpa [htop]
  have : ((!![(0 : ℂ), 1; 0, 0] : Mat2) 0 1) = 0 := hmem
  norm_num at this

lemma strictConvexBadParamSlice_null_addHaar_n2
    (μA : Measure Mat2) [Measure.IsAddHaarMeasure μA] :
    μA strictConvexBadParamSlice_n2 = 0 := by
  have hsub_zero : μA (entry01ZeroSubmodule_n2 : Set Mat2) = 0 :=
    Measure.addHaar_submodule μA entry01ZeroSubmodule_n2 entry01ZeroSubmodule_n2_ne_top
  have hsubset : strictConvexBadParamSlice_n2 ⊆ (entry01ZeroSubmodule_n2 : Set Mat2) := by
    intro A hA
    exact hA.1
  refine le_antisymm ?_ (zero_le _)
  exact (measure_mono hsubset).trans hsub_zero.le

lemma strictConvexBadParamImage_null_addHaar_n2
    (μA : Measure Mat2) [Measure.IsAddHaarMeasure μA] :
    μA (strictConvexBadParamMap_n2 '' strictConvexBadParamSlice_n2) = 0 := by
  exact addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
    (μ := μA)
    differentiableOn_strictConvexBadParamMap_n2
    (strictConvexBadParamSlice_null_addHaar_n2 (μA := μA))

def diagEqualSubmodule_n2 : Submodule ℝ Mat2 where
  carrier := {A : Mat2 | A 0 0 = A 1 1}
  zero_mem' := by simp
  add_mem' := by
    intro A B hA hB
    have hA' : A 0 0 = A 1 1 := hA
    have hB' : B 0 0 = B 1 1 := hB
    change (A + B) 0 0 = (A + B) 1 1
    simp [hA', hB']
  smul_mem' := by
    intro r A hA
    have hA' : A 0 0 = A 1 1 := hA
    change (r • A) 0 0 = (r • A) 1 1
    simpa [hA']

lemma diagEqualSubmodule_n2_ne_top : diagEqualSubmodule_n2 ≠ (⊤ : Submodule ℝ Mat2) := by
  intro htop
  have hmem : (!![(0 : ℂ), 0; 0, 1] : Mat2) ∈ diagEqualSubmodule_n2 := by
    simpa [htop]
  have : ((!![(0 : ℂ), 0; 0, 1] : Mat2) 0 0)
      = ((!![(0 : ℂ), 0; 0, 1] : Mat2) 1 1) := hmem
  norm_num at this

lemma diagEqualSet_null_addHaar_n2
    (μA : Measure Mat2) [Measure.IsAddHaarMeasure μA] :
    μA {A : Mat2 | A 0 0 = A 1 1} = 0 := by
  simpa [diagEqualSubmodule_n2] using
    (Measure.addHaar_submodule μA diagEqualSubmodule_n2 diagEqualSubmodule_n2_ne_top)

def strictConvexBadModelSet_n2 : Set Mat2 :=
  ({A : Mat2 | A 0 0 = A 1 1} ∪
    (strictConvexBadParamMap_n2 '' strictConvexBadParamSlice_n2))

lemma mem_strictConvexBadModelSet_n2_of_exists_rotHermitian_scalar
    (A : Mat2)
    (hrot : ∃ θ : ℝ, rotHermitian A θ ∈ scalarSubmoduleMat2) :
    A ∈ strictConvexBadModelSet_n2 := by
  rcases hrot with ⟨θ, hrotθ⟩
  rcases hrotθ with ⟨z, hzRange⟩
  have hz : rotHermitian A θ = Matrix.scalar (Fin 2) z := hzRange.symm
  rw [strictConvexBadModelSet_n2]
  by_cases hdiag : A 0 0 = A 1 1
  · exact Or.inl hdiag
  · right
    let B : Mat2 := A + (0 - A 0 1) • strictConvexBadE01_n2
    have hB01 : B 0 1 = 0 := by
      simp [B, strictConvexBadE01_n2]
    have hB00 : B 0 0 = A 0 0 := by
      simp [B, strictConvexBadE01_n2]
    have hB10 : B 1 0 = A 1 0 := by
      simp [B, strictConvexBadE01_n2]
    have hB11 : B 1 1 = A 1 1 := by
      simp [B, strictConvexBadE01_n2]
    have hBdiag : B 0 0 ≠ B 1 1 := by
      simpa [hB00, hB11] using hdiag
    have hz01 : (rotHermitian A θ) 0 1 = 0 := by
      simpa [Matrix.scalar_apply] using congrArg (fun M : Mat2 => M 0 1) hz
    have hz00 : (rotHermitian A θ) 0 0 = z := by
      simpa [Matrix.scalar_apply] using congrArg (fun M : Mat2 => M 0 0) hz
    have hz11 : (rotHermitian A θ) 1 1 = z := by
      simpa [Matrix.scalar_apply] using congrArg (fun M : Mat2 => M 1 1) hz
    have hOff : Complex.exp (-((θ : ℂ) * Complex.I)) * A 0 1 +
        Complex.exp ((θ : ℂ) * Complex.I) * star (A 1 0) = 0 := by
      have hhalf :
          (1 / 2 : ℂ) *
            (Complex.exp (-((θ : ℂ) * Complex.I)) * A 0 1
              + Complex.exp ((θ : ℂ) * Complex.I) * star (A 1 0)) = 0 := by
        simpa [rotHermitian] using hz01
      exact (mul_eq_zero.mp hhalf).resolve_left (by norm_num)
    have hDiagEq :
        Complex.exp (-((θ : ℂ) * Complex.I)) * A 0 0
          + Complex.exp ((θ : ℂ) * Complex.I) * star (A 0 0)
          =
        (Complex.exp (-((θ : ℂ) * Complex.I)) * A 1 1
          + Complex.exp ((θ : ℂ) * Complex.I) * star (A 1 1)) := by
      have hhalf00 :
          (1 / 2 : ℂ) *
            (Complex.exp (-((θ : ℂ) * Complex.I)) * A 0 0
              + Complex.exp ((θ : ℂ) * Complex.I) * star (A 0 0)) = z := by
        simpa [rotHermitian] using hz00
      have hhalf11 :
          (1 / 2 : ℂ) *
            (Complex.exp (-((θ : ℂ) * Complex.I)) * A 1 1
              + Complex.exp ((θ : ℂ) * Complex.I) * star (A 1 1)) = z := by
        simpa [rotHermitian] using hz11
      have hhalfEq :
          (1 / 2 : ℂ) *
            (Complex.exp (-((θ : ℂ) * Complex.I)) * A 0 0
              + Complex.exp ((θ : ℂ) * Complex.I) * star (A 0 0))
            =
          (1 / 2 : ℂ) *
            (Complex.exp (-((θ : ℂ) * Complex.I)) * A 1 1
              + Complex.exp ((θ : ℂ) * Complex.I) * star (A 1 1)) :=
        hhalf00.trans hhalf11.symm
      exact mul_left_cancel₀ (show (1 / 2 : ℂ) ≠ 0 by norm_num) hhalfEq
    let δ : ℂ := A 1 1 - A 0 0
    have hδ_ne : δ ≠ 0 := by
      dsimp [δ]
      exact sub_ne_zero.mpr (by simpa [eq_comm] using hdiag)
    have hDiagZero :
        Complex.exp (-((θ : ℂ) * Complex.I)) * δ
          + Complex.exp ((θ : ℂ) * Complex.I) * star δ = 0 := by
      calc
        Complex.exp (-((θ : ℂ) * Complex.I)) * δ
            + Complex.exp ((θ : ℂ) * Complex.I) * star δ
            =
          (Complex.exp (-((θ : ℂ) * Complex.I)) * A 1 1
            + Complex.exp ((θ : ℂ) * Complex.I) * star (A 1 1))
            - (Complex.exp (-((θ : ℂ) * Complex.I)) * A 0 0
              + Complex.exp ((θ : ℂ) * Complex.I) * star (A 0 0)) := by
              dsimp [δ]
              simp [map_sub]
              ring
        _ = 0 := sub_eq_zero.mpr hDiagEq.symm
    let eplus : ℂ := Complex.exp ((θ : ℂ) * Complex.I)
    let eminus : ℂ := Complex.exp (-((θ : ℂ) * Complex.I))
    let e2 : ℂ := eplus * eplus
    have heplus_eminus : eplus * eminus = 1 := by
      dsimp [eplus, eminus]
      calc
        Complex.exp ((θ : ℂ) * Complex.I) * Complex.exp (-((θ : ℂ) * Complex.I))
            = Complex.exp (((θ : ℂ) * Complex.I) + (-((θ : ℂ) * Complex.I))) := by
              simpa using
                (Complex.exp_add ((θ : ℂ) * Complex.I) (-((θ : ℂ) * Complex.I))).symm
        _ = 1 := by simp
    have hOff' : A 0 1 + e2 * star (A 1 0) = 0 := by
      have hOff'base :
          eminus * A 0 1 + eplus * star (A 1 0) = 0 := by
        simpa [eplus, eminus] using hOff
      have := congrArg (fun t : ℂ => eplus * t) hOff'base
      have hmul :
          (eplus * eminus) * A 0 1 + (eplus * eplus) * star (A 1 0) = 0 := by
        simpa [mul_add, mul_assoc] using this
      simpa [e2, heplus_eminus] using hmul
    have hDiagZero' : δ + e2 * star δ = 0 := by
      have hDiagZeroBase :
          eminus * δ + eplus * star δ = 0 := by
        simpa [eplus, eminus] using hDiagZero
      have := congrArg (fun t : ℂ => eplus * t) hDiagZeroBase
      have hmul :
          (eplus * eminus) * δ + (eplus * eplus) * star δ = 0 := by
        simpa [mul_add, mul_assoc] using this
      simpa [e2, heplus_eminus] using hmul
    have hstarδ_ne : star δ ≠ 0 := star_ne_zero.mpr hδ_ne
    have he2 : e2 = -δ * (star δ)⁻¹ := by
      apply (eq_mul_inv_iff_mul_eq₀ hstarδ_ne).2
      exact eq_neg_of_add_eq_zero_right hDiagZero'
    have hRelation : A 0 1 = strictConvexBadTargetB_n2 A := by
      unfold strictConvexBadTargetB_n2
      calc
        A 0 1 = -(e2 * star (A 1 0)) := eq_neg_of_add_eq_zero_left hOff'
        _ = star (A 1 0) * (δ * (star δ)⁻¹) := by
          rw [he2]
          ring
        _ = star (A 1 0) * ((A 1 1 - A 0 0) * (star (A 1 1 - A 0 0))⁻¹) := by
          simp [δ]
        _ = strictConvexBadTargetB_n2 A := rfl
    have hB_target : strictConvexBadTargetB_n2 B = A 0 1 := by
      calc
        strictConvexBadTargetB_n2 B
            = star (B 1 0) * ((B 1 1 - B 0 0) * (star (B 1 1 - B 0 0))⁻¹) := rfl
        _ = star (A 1 0) * ((A 1 1 - A 0 0) * (star (A 1 1 - A 0 0))⁻¹) := by
          simp [hB10, hB11, hB00]
        _ = A 0 1 := by simpa [strictConvexBadTargetB_n2] using hRelation.symm
    refine ⟨B, ⟨hB01, hBdiag⟩, ?_⟩
    rw [strictConvexBadParamMap_n2, hB_target, hB01, sub_zero]
    ext i j
    fin_cases i <;> fin_cases j
    · simp [B, strictConvexBadE01_n2]
    · simp [B, strictConvexBadE01_n2]
    · simp [B, strictConvexBadE01_n2]
    · simp [B, strictConvexBadE01_n2]

theorem strictConvexBadModelSet_null_addHaar_n2
    (μA : Measure Mat2) [Measure.IsAddHaarMeasure μA] :
    μA strictConvexBadModelSet_n2 = 0 := by
  rw [strictConvexBadModelSet_n2]
  exact measure_union_null
    (diagEqualSet_null_addHaar_n2 (μA := μA))
    (strictConvexBadParamImage_null_addHaar_n2 (μA := μA))

theorem strictConvex_badset_subset_model_n2_of_exists_rotHermitian_scalar
    (hGeom :
      ∀ A : Mat2, ¬ StrictConvex ℝ (numericalRangeMat A) →
        ∃ θ : ℝ, rotHermitian A θ ∈ scalarSubmoduleMat2) :
    {A : Mat2 | ¬ StrictConvex ℝ (numericalRangeMat A)} ⊆ strictConvexBadModelSet_n2 := by
  intro A hA
  exact mem_strictConvexBadModelSet_n2_of_exists_rotHermitian_scalar A (hGeom A hA)

theorem strictConvex_badset_null_addHaar_n2_of_subset_model
    (μA : Measure Mat2) [Measure.IsAddHaarMeasure μA]
    (hsubset :
      {A : Mat2 | ¬ StrictConvex ℝ (numericalRangeMat A)} ⊆ strictConvexBadModelSet_n2) :
    μA {A : Mat2 | ¬ StrictConvex ℝ (numericalRangeMat A)} = 0 := by
  have hmodel_zero : μA strictConvexBadModelSet_n2 = 0 :=
    strictConvexBadModelSet_null_addHaar_n2 (μA := μA)
  refine le_antisymm ?_ (zero_le _)
  exact (measure_mono hsubset).trans hmodel_zero.le

theorem strictConvex_badset_null_addHaar_n2_of_exists_rotHermitian_scalar
    (μA : Measure Mat2) [Measure.IsAddHaarMeasure μA]
    (hGeom :
      ∀ A : Mat2, ¬ StrictConvex ℝ (numericalRangeMat A) →
        ∃ θ : ℝ, rotHermitian A θ ∈ scalarSubmoduleMat2) :
    μA {A : Mat2 | ¬ StrictConvex ℝ (numericalRangeMat A)} = 0 := by
  apply strictConvex_badset_null_addHaar_n2_of_subset_model (μA := μA)
  exact strictConvex_badset_subset_model_n2_of_exists_rotHermitian_scalar hGeom

/--
`(SC)` bad-set null theorem for the concrete smoothness and additive Haar measure, from the
strict-convexity subset-model reduction.
-/
theorem condSC_badset_null_concreteSmooth_addHaar_n2_of_subset_model
    (μA : Measure Mat2) [Measure.IsAddHaarMeasure μA]
    (hStrict_subset :
      {A : Mat2 | ¬ StrictConvex ℝ (numericalRangeMat A)} ⊆ strictConvexBadModelSet_n2) :
    μA {A : Mat2 | ¬ CondSC SmoothBoundarySimpleAtZero_n2 A} = 0 := by
  have hStrict_bad : μA {A : Mat2 | ¬ StrictConvex ℝ (numericalRangeMat A)} = 0 :=
    strictConvex_badset_null_addHaar_n2_of_subset_model (μA := μA) hStrict_subset
  exact condSC_badset_null_of_components (μA := μA) SmoothBoundarySimpleAtZero_n2
    (smoothBoundarySimpleAtZero_badset_null_addHaar_n2 (μA := μA)) hStrict_bad

theorem condSC_badset_null_concreteSmooth_addHaar_n2
    (μA : Measure Mat2) [IsAddHaarMeasure μA]
    (hStrict_bad : μA {A : Mat2 | ¬ StrictConvex ℝ (numericalRangeMat A)} = 0) :
    μA {A : Mat2 | ¬ CondSC SmoothBoundarySimpleAtZero_n2 A} = 0 := by
  exact condSC_badset_null_of_components (μA := μA) SmoothBoundarySimpleAtZero_n2
    (smoothBoundarySimpleAtZero_badset_null_addHaar_n2 (μA := μA)) hStrict_bad

/--
For `n = 2` with an additive Haar matrix measure, the `(S)` side is unconditional:
density reduces to the single `(SC)` bad-set-null hypothesis.
-/
theorem lem_degen_cTex_n2_addHaar_from_SC_bad
    (μA : Measure Mat2) [Measure.IsOpenPosMeasure μA] [SFinite μA] [IsAddHaarMeasure μA]
    (ν : Measure ℝ) [SFinite ν]
    (SmoothBoundary : Mat2 → Prop)
    (hSC_bad : μA {A : Mat2 | ¬ CondSC SmoothBoundary A} = 0) :
    Dense {A : Mat2 | CondSC SmoothBoundary A ∧ CondS ν A} := by
  have hS_pointwise : ∀ θ : ℝ, μA {A : Mat2 | ¬ HasSimpleSpectrum (rotHermitian A θ)} = 0 := by
    intro θ
    exact hS_pointwise_null_addHaar_n2 (μA := μA) θ
  exact lem_degen_cTex_n_ge_two 2 (by decide) μA ν SmoothBoundary
    hSC_bad hS_measurable_badset_n2 hS_pointwise

/--
Counterexample showing `(1)` cannot be proved unconditionally at this abstraction level:
if `SmoothBoundary := False`, then the `(SC)` bad set is all matrices.
-/
theorem hSC_badset_null_fails_for_false_smooth :
    ¬ ((Measure.dirac (0 : Mat2)) {A : Mat2 | ¬ CondSC (fun _ => False) A} = 0) := by
  have h1 : (Measure.dirac (0 : Mat2)) {A : Mat2 | ¬ CondSC (fun _ => False) A} = 1 := by
    have hset : {A : Mat2 | ¬ CondSC (fun _ => False) A} = Set.univ := by
      ext A
      simp [CondSC]
    rw [hset]
    simp
  intro h0
  have : (1 : ENNReal) = 0 := by
    calc
      (1 : ENNReal)
          = (Measure.dirac (0 : Mat2)) {A : Mat2 | ¬ CondSC (fun _ => False) A} := h1.symm
      _ = 0 := h0
  exact one_ne_zero this

/--
Counterexample showing `(3)` cannot be true for arbitrary matrix measures:
for the Dirac mass at `0`, every angle slice has positive bad-set mass.
-/
theorem hS_pointwise_null_fails_for_dirac_n2 :
    ¬ (∀ θ : ℝ, (Measure.dirac (0 : Mat2))
      {A : Mat2 | ¬ HasSimpleSpectrum (rotHermitian A θ)} = 0) := by
  intro h
  have h1 :
      (Measure.dirac (0 : Mat2))
      {A : Mat2 | ¬ HasSimpleSpectrum (rotHermitian A 0)} = 1 := by
    have h0mem : (0 : Mat2) ∈ {A : Mat2 | ¬ HasSimpleSpectrum (rotHermitian A 0)} := by
      simp [HasSimpleSpectrum, rotHermitian, Matrix.discr_fin_two, Matrix.det_zero]
    simp [h0mem]
  have h0 :
      (Measure.dirac (0 : Mat2))
      {A : Mat2 | ¬ HasSimpleSpectrum (rotHermitian A 0)} = 0 := h 0
  have : (1 : ENNReal) = 0 := by
    calc
      (1 : ENNReal)
          = (Measure.dirac (0 : Mat2))
            {A : Mat2 | ¬ HasSimpleSpectrum (rotHermitian A 0)} := h1.symm
      _ = 0 := h0
  exact one_ne_zero this

/--
At the present abstraction level (where `SmoothBoundary` is an arbitrary predicate),
the fully unconditional schema is false.
-/
theorem not_unconditional_lem_degen_schema (n : ℕ) :
    ¬ (∀ (ν : Measure ℝ) (SmoothBoundary : Mat n → Prop),
        Dense {A : Mat n | CondSC SmoothBoundary A ∧ CondS ν A}) := by
  intro hAll
  have hDense :
      Dense {A : Mat n | CondSC (fun _ => False) A ∧ CondS Measure.count A} :=
    hAll Measure.count (fun _ => False)
  have hEmpty :
      {A : Mat n | CondSC (fun _ => False) A ∧ CondS Measure.count A} = (∅ : Set (Mat n)) := by
    ext A
    simp [CondSC]
  have hEmptyDense : Dense (∅ : Set (Mat n)) := by
    simpa [hEmpty] using hDense
  have hEq : (∅ : Set (Mat n)) = Set.univ := by
    simpa [dense_iff_closure_eq] using hEmptyDense
  exact Set.empty_ne_univ hEq

end MyProject
