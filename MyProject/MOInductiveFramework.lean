import MyProject.Basic

noncomputable section

open scoped BigOperators

namespace MyProject

section Shell

variable {E : Type*} [AddCommMonoid E]

/-- Degree shell built from all pair-indices `j+k=r`. -/
def Delta (term : ℕ → ℕ → E) (r : ℕ) : E :=
  ∑ j ∈ Finset.range (r + 1), term j (r - j)

/-- Truncated first-variation vector up to degree `d`. -/
def w_d (term : ℕ → ℕ → E) (d : ℕ) : E :=
  ∑ r ∈ Finset.range (d + 1), Delta term r

lemma w_d_eq_sum_shells (term : ℕ → ℕ → E) (d : ℕ) :
    w_d term d = ∑ r ∈ Finset.range (d + 1), Delta term r := by
  rfl

lemma w_d_succ (term : ℕ → ℕ → E) (d : ℕ) :
    w_d term (d + 1) = w_d term d + Delta term (d + 1) := by
  simp [w_d, Finset.sum_range_succ, add_assoc]

lemma w_d_zero (term : ℕ → ℕ → E) :
    w_d term 0 = Delta term 0 := by
  simp [w_d]

lemma w_d_one (term : ℕ → ℕ → E) :
    w_d term 1 = Delta term 0 + Delta term 1 := by
  calc
    w_d term 1 = w_d term 0 + Delta term 1 := by
      simpa using w_d_succ term 0
    _ = Delta term 0 + Delta term 1 := by
      simp [w_d_zero]

lemma w_d_two (term : ℕ → ℕ → E) :
    w_d term 2 = Delta term 0 + Delta term 1 + Delta term 2 := by
  calc
    w_d term 2 = w_d term 1 + Delta term 2 := by
      simpa [Nat.add_assoc] using w_d_succ term 1
    _ = Delta term 0 + Delta term 1 + Delta term 2 := by
      simp [w_d_one, add_assoc]

end Shell

section MO

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- `V3 = span{x, Ax, A* x}`. For adjoint-based applications, set `Astar = Aᴴ`. -/
def V3 (A Astar : E →ₗ[ℂ] E) (x : E) : Submodule ℂ E :=
  Submodule.span ℂ ({x, A x, Astar x} : Set E)

/-- Truncated multilinear first-variation functional. -/
def D_d (term : ℕ → ℕ → E) (d : ℕ) (ξ : E) : ℝ :=
  Complex.re (inner ℂ ξ (w_d term d))

/-- Finite-degree MO statement. -/
def MO_d (A Astar : E →ₗ[ℂ] E) (x : E) (term : ℕ → ℕ → E) (d : ℕ) : Prop :=
  ∀ ξ, ξ ∈ (V3 A Astar x)ᗮ → D_d term d ξ = 0

lemma exists_w_d_representation (term : ℕ → ℕ → E) (d : ℕ) :
    ∃ w : E, ∀ ξ : E, D_d term d ξ = Complex.re (inner ℂ ξ w) := by
  refine ⟨w_d term d, ?_⟩
  intro ξ
  rfl

lemma MO_d_of_w_d_mem_V3
    (A Astar : E →ₗ[ℂ] E) (x : E) (term : ℕ → ℕ → E) (d : ℕ)
    (hwd : w_d term d ∈ V3 A Astar x) :
    MO_d A Astar x term d := by
  intro ξ hξ
  have hInnerRight : inner ℂ (w_d term d) ξ = 0 :=
    (Submodule.mem_orthogonal (V3 A Astar x) ξ).1 hξ _ hwd
  have hInnerLeft : inner ℂ ξ (w_d term d) = 0 :=
    (inner_eq_zero_symm).1 hInnerRight
  simp [D_d, hInnerLeft]

lemma w_d_mem_V3_of_MO_d
    [FiniteDimensional ℂ E]
    (A Astar : E →ₗ[ℂ] E) (x : E) (term : ℕ → ℕ → E) (d : ℕ)
    (hMO : MO_d A Astar x term d) :
    w_d term d ∈ V3 A Astar x := by
  have hInDoubleOrth : w_d term d ∈ (V3 A Astar x)ᗮᗮ := by
    rw [Submodule.mem_orthogonal]
    intro ξ hξ
    have hRe : Complex.re (inner ℂ ξ (w_d term d)) = 0 := by
      simpa [D_d] using hMO ξ hξ
    have hIRe : Complex.re (inner ℂ (Complex.I • ξ) (w_d term d)) = 0 := by
      have hIorth : Complex.I • ξ ∈ (V3 A Astar x)ᗮ :=
        Submodule.smul_mem ((V3 A Astar x)ᗮ) Complex.I hξ
      simpa [D_d] using hMO (Complex.I • ξ) hIorth
    have hIm : (inner ℂ ξ (w_d term d)).im = 0 := by
      simpa [inner_smul_left] using hIRe
    exact Complex.ext (by simpa using hRe) (by simpa using hIm)
  simpa [Submodule.orthogonal_orthogonal] using hInDoubleOrth

theorem MO_d_iff_w_d_mem_V3
    [FiniteDimensional ℂ E]
    (A Astar : E →ₗ[ℂ] E) (x : E) (term : ℕ → ℕ → E) (d : ℕ) :
    MO_d A Astar x term d ↔ w_d term d ∈ V3 A Astar x := by
  constructor
  · exact w_d_mem_V3_of_MO_d A Astar x term d
  · exact MO_d_of_w_d_mem_V3 A Astar x term d

/-- Induction target `P(d): w_d ∈ V3`. -/
def P (A Astar : E →ₗ[ℂ] E) (x : E) (term : ℕ → ℕ → E) (d : ℕ) : Prop :=
  w_d term d ∈ V3 A Astar x

lemma P_step_of_shell
    (A Astar : E →ₗ[ℂ] E) (x : E) (term : ℕ → ℕ → E)
    {d : ℕ}
    (hPd : P A Astar x term d)
    (hDelta : Delta term (d + 1) ∈ V3 A Astar x) :
    P A Astar x term (d + 1) := by
  have hw : w_d term (d + 1) = w_d term d + Delta term (d + 1) := w_d_succ term d
  rw [P, hw]
  exact Submodule.add_mem (V3 A Astar x) hPd hDelta

lemma P_zero_of_shell
    (A Astar : E →ₗ[ℂ] E) (x : E) (term : ℕ → ℕ → E)
    (h0 : Delta term 0 ∈ V3 A Astar x) :
    P A Astar x term 0 := by
  rw [P, w_d_zero]
  exact h0

lemma P_one_of_shells
    (A Astar : E →ₗ[ℂ] E) (x : E) (term : ℕ → ℕ → E)
    (h0 : Delta term 0 ∈ V3 A Astar x)
    (h1 : Delta term 1 ∈ V3 A Astar x) :
    P A Astar x term 1 := by
  rw [P, w_d_one]
  exact Submodule.add_mem (V3 A Astar x) h0 h1

lemma P_two_of_shells
    (A Astar : E →ₗ[ℂ] E) (x : E) (term : ℕ → ℕ → E)
    (h0 : Delta term 0 ∈ V3 A Astar x)
    (h1 : Delta term 1 ∈ V3 A Astar x)
    (h2 : Delta term 2 ∈ V3 A Astar x) :
    P A Astar x term 2 := by
  rw [P, w_d_two]
  exact Submodule.add_mem (V3 A Astar x)
    (Submodule.add_mem (V3 A Astar x) h0 h1) h2

lemma P_all_of_shell_bases_and_tail
    (A Astar : E →ₗ[ℂ] E) (x : E) (term : ℕ → ℕ → E)
    (h0 : Delta term 0 ∈ V3 A Astar x)
    (h1 : Delta term 1 ∈ V3 A Astar x)
    (h2 : Delta term 2 ∈ V3 A Astar x)
    (hTail : ∀ r : ℕ, 3 ≤ r → Delta term r ∈ V3 A Astar x) :
    ∀ d : ℕ, P A Astar x term d := by
  have hP0 : P A Astar x term 0 := P_zero_of_shell A Astar x term h0
  have hP1 : P A Astar x term 1 := P_one_of_shells A Astar x term h0 h1
  have hP2 : P A Astar x term 2 := P_two_of_shells A Astar x term h0 h1 h2
  have h_ge2 : ∀ n : ℕ, P A Astar x term (n + 2) := by
    intro n
    induction n with
    | zero =>
        simpa using hP2
    | succ n ihn =>
        have hDelta : Delta term (n + 3) ∈ V3 A Astar x := by
          have hge : 3 ≤ n + 3 := by omega
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hTail (n + 3) hge
        have hstep : P A Astar x term ((n + 2) + 1) :=
          P_step_of_shell A Astar x term (d := n + 2) ihn hDelta
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hstep
  intro d
  cases d with
  | zero =>
      simpa using hP0
  | succ d =>
      cases d with
      | zero =>
          simpa using hP1
      | succ d =>
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h_ge2 d

lemma MO_d_all_of_shell_bases_and_tail
    [FiniteDimensional ℂ E]
    (A Astar : E →ₗ[ℂ] E) (x : E) (term : ℕ → ℕ → E)
    (h0 : Delta term 0 ∈ V3 A Astar x)
    (h1 : Delta term 1 ∈ V3 A Astar x)
    (h2 : Delta term 2 ∈ V3 A Astar x)
    (hTail : ∀ r : ℕ, 3 ≤ r → Delta term r ∈ V3 A Astar x) :
    ∀ d : ℕ, MO_d A Astar x term d := by
  intro d
  have hP : P A Astar x term d := P_all_of_shell_bases_and_tail A Astar x term h0 h1 h2 hTail d
  exact MO_d_of_w_d_mem_V3 A Astar x term d hP

end MO

end MyProject

