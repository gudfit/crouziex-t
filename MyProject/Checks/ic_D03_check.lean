import Mathlib

-- Fast local checker for the D03 block.
-- Run from repo root:
--   lake env lean MyProject/Checks/ic_D03_check.lean

abbrev E3 := EuclideanSpace ℂ (Fin 3)

noncomputable def UpperTri (a b c : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, a, c;
     0, 0, b;
     0, 0, 0]

def D03Hyp (a b : ℂ) : Prop :=
  ∀ x : E3, ‖x‖ = 1 →
    ∃ alpha beta : ℂ,
      Matrix.mulVec (UpperTri a b 0).conjTranspose x.ofLp =
        alpha • x.ofLp + beta • Matrix.mulVec (UpperTri a b 0) x.ofLp ∧ ‖beta‖ = 1

lemma d03_zero_constraints (a b : ℂ) (h_prop : D03Hyp a b) :
    ‖a‖ = 0 ∧ ‖b‖ = 0 := by
  let e0 : E3 := EuclideanSpace.single (0 : Fin 3) (1 : ℂ)
  have he0_norm : ‖e0‖ = 1 := by
    simp [e0]
  rcases h_prop e0 he0_norm with ⟨alpha0, beta0, h_eq0, _hbeta0⟩
  have ha0 : a = 0 := by
    have h_comp1 := congr_fun h_eq0 1
    simp [UpperTri, e0, Matrix.mulVec, dotProduct] at h_comp1
    exact h_comp1

  let e1 : E3 := EuclideanSpace.single (1 : Fin 3) (1 : ℂ)
  have he1_norm : ‖e1‖ = 1 := by
    simp [e1]
  rcases h_prop e1 he1_norm with ⟨alpha1, beta1, h_eq1, _hbeta1⟩
  have hb0 : b = 0 := by
    have h_comp2 := congr_fun h_eq1 2
    simp [UpperTri, e1, Matrix.mulVec, dotProduct] at h_comp2
    exact h_comp2

  constructor <;> simp [ha0, hb0]

lemma d03_hyp_holds_for_zero : D03Hyp 0 0 := by
  intro x hx
  refine ⟨0, 1, ?_, by simp⟩
  ext i
  fin_cases i <;> simp [UpperTri, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

lemma d03_old_goal_false :
    ¬ (∀ a b : ℂ, D03Hyp a b → ‖a‖ = Real.sqrt 2 ∧ ‖b‖ = Real.sqrt 2) := by
  intro h
  have h0 := h 0 0 d03_hyp_holds_for_zero
  have hsqrt : (0 : ℝ) = Real.sqrt 2 := by
    simpa using h0.1
  have hsqrt_ne_zero : (Real.sqrt 2) ≠ (0 : ℝ) := by
    positivity
  exact hsqrt_ne_zero hsqrt.symm
