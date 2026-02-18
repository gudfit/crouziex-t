import MyProject.MOInductiveFramework
import MyProject.MO4NonHermitian

noncomputable section

open scoped BigOperators

namespace MyProject

/--
Concrete finite-degree MO package in the existing `N=4` model.
The `term j k` field is the degree-`(j,k)` contribution to the vector-valued first variation.
-/
structure MO4FiniteData where
  x : E4MO
  v : E4MO
  thetaStar : ℝ
  term : ℕ → ℕ → E4MO

/-- Concrete shell `Δ_r` in the `N=4` model. -/
def MO4Delta (D : MO4FiniteData) (r : ℕ) : E4MO :=
  Delta D.term r

/-- Concrete truncated first-variation vector `w_d`. -/
def MO4w_d (D : MO4FiniteData) (d : ℕ) : E4MO :=
  w_d D.term d

/-- Concrete real first-variation functional `D_d(ξ)=Re⟪ξ,w_d⟫`. -/
def MO4D_d (D : MO4FiniteData) (d : ℕ) (ξ : E4MO) : ℝ :=
  D_d D.term d ξ

/-- Concrete finite-degree MO statement in the `N=4` shifted model. -/
def MO4_d (D : MO4FiniteData) (d : ℕ) : Prop :=
  ∀ ξ, ξ ∈ (shiftedSpan4 D.x)ᗮ → MO4D_d D d ξ = 0

lemma MO4w_d_eq_sum_shells (D : MO4FiniteData) (d : ℕ) :
    MO4w_d D d = ∑ r ∈ Finset.range (d + 1), MO4Delta D r := by
  simpa [MO4w_d, MO4Delta] using w_d_eq_sum_shells D.term d

lemma MO4w_d_succ (D : MO4FiniteData) (d : ℕ) :
    MO4w_d D (d + 1) = MO4w_d D d + MO4Delta D (d + 1) := by
  simpa [MO4w_d, MO4Delta] using w_d_succ D.term d

lemma MO4w_d_zero (D : MO4FiniteData) :
    MO4w_d D 0 = MO4Delta D 0 := by
  simpa [MO4w_d, MO4Delta] using w_d_zero D.term

lemma MO4w_d_one (D : MO4FiniteData) :
    MO4w_d D 1 = MO4Delta D 0 + MO4Delta D 1 := by
  simpa [MO4w_d, MO4Delta] using w_d_one D.term

lemma MO4w_d_two (D : MO4FiniteData) :
    MO4w_d D 2 = MO4Delta D 0 + MO4Delta D 1 + MO4Delta D 2 := by
  simpa [MO4w_d, MO4Delta] using w_d_two D.term

lemma shiftedSpan4_eq_V3 (x : E4MO) :
    shiftedSpan4 x = V3 A4Lin A4AdjLin x := rfl

lemma MO4_d_iff_generic (D : MO4FiniteData) (d : ℕ) :
    MO4_d D d ↔ MO_d A4Lin A4AdjLin D.x D.term d := by
  simp [MO4_d, MO4D_d, MO_d, D_d, shiftedSpan4_eq_V3]

lemma exists_MO4_w_d_representation (D : MO4FiniteData) (d : ℕ) :
    ∃ w : E4MO, ∀ ξ : E4MO, MO4D_d D d ξ = Complex.re (inner ℂ ξ w) := by
  simpa [MO4D_d] using exists_w_d_representation (E := E4MO) D.term d

theorem MO4_d_iff_w_d_mem_shiftedSpan4 (D : MO4FiniteData) (d : ℕ) :
    MO4_d D d ↔ MO4w_d D d ∈ shiftedSpan4 D.x := by
  have h :=
    (MO_d_iff_w_d_mem_V3 (E := E4MO) A4Lin A4AdjLin D.x D.term d)
  simpa [MO4_d, MO4w_d, MO4D_d, MO_d, D_d, shiftedSpan4_eq_V3] using h

theorem MO4_w_d_all_mem_shiftedSpan4_of_shell_bases_and_tail
    (D : MO4FiniteData)
    (h0 : MO4Delta D 0 ∈ shiftedSpan4 D.x)
    (h1 : MO4Delta D 1 ∈ shiftedSpan4 D.x)
    (h2 : MO4Delta D 2 ∈ shiftedSpan4 D.x)
    (hTail : ∀ r : ℕ, 3 ≤ r → MO4Delta D r ∈ shiftedSpan4 D.x) :
    ∀ d : ℕ, MO4w_d D d ∈ shiftedSpan4 D.x := by
  intro d
  have h :=
    P_all_of_shell_bases_and_tail (E := E4MO) A4Lin A4AdjLin D.x D.term
      (by simpa [MO4Delta, shiftedSpan4_eq_V3] using h0)
      (by simpa [MO4Delta, shiftedSpan4_eq_V3] using h1)
      (by simpa [MO4Delta, shiftedSpan4_eq_V3] using h2)
      (by
        intro r hr
        simpa [MO4Delta, shiftedSpan4_eq_V3] using hTail r hr)
      d
  simpa [MO4w_d, shiftedSpan4_eq_V3] using h

lemma MO4w_d_mem_shiftedSpan4_d0_of_shell0
    (D : MO4FiniteData)
    (h0 : MO4Delta D 0 ∈ shiftedSpan4 D.x) :
    MO4w_d D 0 ∈ shiftedSpan4 D.x := by
  simpa [MO4w_d_zero] using h0

lemma MO4w_d_mem_shiftedSpan4_d1_of_shell01
    (D : MO4FiniteData)
    (h0 : MO4Delta D 0 ∈ shiftedSpan4 D.x)
    (h1 : MO4Delta D 1 ∈ shiftedSpan4 D.x) :
    MO4w_d D 1 ∈ shiftedSpan4 D.x := by
  rw [MO4w_d_one]
  exact Submodule.add_mem (shiftedSpan4 D.x) h0 h1

lemma MO4w_d_mem_shiftedSpan4_d2_of_shell012
    (D : MO4FiniteData)
    (h0 : MO4Delta D 0 ∈ shiftedSpan4 D.x)
    (h1 : MO4Delta D 1 ∈ shiftedSpan4 D.x)
    (h2 : MO4Delta D 2 ∈ shiftedSpan4 D.x) :
    MO4w_d D 2 ∈ shiftedSpan4 D.x := by
  rw [MO4w_d_two]
  exact Submodule.add_mem (shiftedSpan4 D.x)
    (Submodule.add_mem (shiftedSpan4 D.x) h0 h1) h2

lemma MO4w_d_mem_shiftedSpan4_step
    (D : MO4FiniteData)
    {d : ℕ}
    (hwd : MO4w_d D d ∈ shiftedSpan4 D.x)
    (hDelta : MO4Delta D (d + 1) ∈ shiftedSpan4 D.x) :
    MO4w_d D (d + 1) ∈ shiftedSpan4 D.x := by
  rw [MO4w_d_succ]
  exact Submodule.add_mem (shiftedSpan4 D.x) hwd hDelta

theorem MO4_d_all_of_shell_bases_and_tail
    (D : MO4FiniteData)
    (h0 : MO4Delta D 0 ∈ shiftedSpan4 D.x)
    (h1 : MO4Delta D 1 ∈ shiftedSpan4 D.x)
    (h2 : MO4Delta D 2 ∈ shiftedSpan4 D.x)
    (hTail : ∀ r : ℕ, 3 ≤ r → MO4Delta D r ∈ shiftedSpan4 D.x) :
    ∀ d : ℕ, MO4_d D d := by
  intro d
  have hmem : MO4w_d D d ∈ shiftedSpan4 D.x :=
    MO4_w_d_all_mem_shiftedSpan4_of_shell_bases_and_tail D h0 h1 h2 hTail d
  exact (MO4_d_iff_w_d_mem_shiftedSpan4 D d).2 hmem

end MyProject
