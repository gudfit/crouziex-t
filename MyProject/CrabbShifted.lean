import MyProject.Basic
import Mathlib.RingTheory.Nilpotent.Basic

noncomputable section

open scoped BigOperators

namespace MyProject

section ShiftedScaled

variable {n : ℕ}

abbrev shiftedScaled (α : ℂ) (K : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  (1 : Matrix (Fin n) (Fin n) ℂ) - α • K

abbrev neumannSeries (α : ℂ) (K : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  Finset.sum (Finset.range n) (fun k => (α • K) ^ k)

lemma neumannSeries_eq_sum_smul_pow (α : ℂ) (K : Matrix (Fin n) (Fin n) ℂ) :
    neumannSeries (n := n) α K = Finset.sum (Finset.range n) (fun k => α ^ k • K ^ k) := by
  simp [neumannSeries, smul_pow]

lemma shiftedScaled_mul_neumannSeries (α : ℂ) (K : Matrix (Fin n) (Fin n) ℂ)
    (hK : K ^ n = 0) :
    shiftedScaled (n := n) α K * neumannSeries (n := n) α K = 1 := by
  have hpow0 : (α • K) ^ n = 0 := by
    simp [smul_pow, hK]
  calc
    shiftedScaled (n := n) α K * neumannSeries (n := n) α K
        = 1 - (α • K) ^ n := by
          simpa [shiftedScaled, neumannSeries] using (mul_neg_geom_sum (α • K) n)
    _ = 1 := by simp [hpow0]

lemma neumannSeries_mul_shiftedScaled (α : ℂ) (K : Matrix (Fin n) (Fin n) ℂ)
    (hK : K ^ n = 0) :
    neumannSeries (n := n) α K * shiftedScaled (n := n) α K = 1 := by
  have hpow0 : (α • K) ^ n = 0 := by
    simp [smul_pow, hK]
  calc
    neumannSeries (n := n) α K * shiftedScaled (n := n) α K
        = 1 - (α • K) ^ n := by
          simpa [shiftedScaled, neumannSeries] using (geom_sum_mul_neg (α • K) n)
    _ = 1 := by simp [hpow0]

lemma isUnit_shiftedScaled (α : ℂ) (K : Matrix (Fin n) (Fin n) ℂ) (hK : K ^ n = 0) :
    IsUnit (shiftedScaled (n := n) α K) := by
  refine ⟨⟨shiftedScaled (n := n) α K, neumannSeries (n := n) α K, ?_, ?_⟩, rfl⟩
  · exact shiftedScaled_mul_neumannSeries (n := n) α K hK
  · exact neumannSeries_mul_shiftedScaled (n := n) α K hK

end ShiftedScaled

section CrabbSpecialization

variable {n : ℕ}

abbrev shiftedCrabb (n : ℕ) (α : ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  shiftedScaled (n := n) α (CrabbMatrix n)

abbrev shiftedCrabbNeumann (n : ℕ) (α : ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  neumannSeries (n := n) α (CrabbMatrix n)

/--
For Crabb matrices, `K_n^n = 0`, so `I - αK_n` times the finite Neumann series is identity.
-/
lemma shiftedCrabb_mul_neumann (α : ℂ) :
    shiftedCrabb n α * shiftedCrabbNeumann n α = 1 := by
  exact shiftedScaled_mul_neumannSeries (n := n) α (CrabbMatrix n)
    (crabbMatrix_pow_n_eq_zero n)

lemma neumann_mul_shiftedCrabb (α : ℂ) :
    shiftedCrabbNeumann n α * shiftedCrabb n α = 1 := by
  exact neumannSeries_mul_shiftedScaled (n := n) α (CrabbMatrix n)
    (crabbMatrix_pow_n_eq_zero n)

lemma isUnit_shiftedCrabb (α : ℂ) :
    IsUnit (shiftedCrabb n α) := by
  exact isUnit_shiftedScaled (n := n) α (CrabbMatrix n)
    (crabbMatrix_pow_n_eq_zero n)

/-- Concrete scalar used in the shifted/scaled Crabb test: `α = 1 + √2`. -/
noncomputable def alphaSqrtTwo : ℂ := (1 + Real.sqrt 2 : ℂ)

abbrev shiftedCrabbSqrtTwo (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  shiftedCrabb n alphaSqrtTwo

abbrev shiftedCrabbNeumannSqrtTwo (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  shiftedCrabbNeumann n alphaSqrtTwo

lemma shiftedCrabbSqrtTwo_mul_neumann :
    shiftedCrabbSqrtTwo n * shiftedCrabbNeumannSqrtTwo n = 1 := by
  exact shiftedCrabb_mul_neumann (n := n) alphaSqrtTwo

lemma neumann_mul_shiftedCrabbSqrtTwo :
    shiftedCrabbNeumannSqrtTwo n * shiftedCrabbSqrtTwo n = 1 := by
  exact neumann_mul_shiftedCrabb (n := n) alphaSqrtTwo

lemma isUnit_shiftedCrabbSqrtTwo :
    IsUnit (shiftedCrabbSqrtTwo n) := by
  exact isUnit_shiftedCrabb (n := n) alphaSqrtTwo

end CrabbSpecialization

end MyProject
