import MyProject.MOInductiveConcrete

noncomputable section

open scoped BigOperators

namespace MyProject

section Step7

variable {E : Type*} [AddCommMonoid E] [Module ℂ E]

/-- Resolvent-shell coefficient profile: coefficients depend only on `j+k+1`. -/
def cjkFromNatCoeff (a : ℕ → ℂ) (j k : ℕ) : ℂ :=
  a (j + k + 1)

lemma cjkFromNatCoeff_hankel (a : ℕ → ℂ) {j k j' k' : ℕ}
    (h : j + k = j' + k') :
    cjkFromNatCoeff a j k = cjkFromNatCoeff a j' k' := by
  simp [cjkFromNatCoeff, h]

lemma cjkFromNatCoeff_on_shell (a : ℕ → ℂ) (r j : ℕ) (hj : j ≤ r) :
    cjkFromNatCoeff a j (r - j) = a (r + 1) := by
  simp [cjkFromNatCoeff, Nat.add_sub_of_le hj]

lemma cjkFromCoeff4_eq_cjkFromNatCoeff
    (a : Fin 4 → ℂ) (j k : Fin 3) :
    cjkFromCoeff4 a j k = cjkFromNatCoeff (coeffAt4 a) j.1 k.1 := rfl

lemma cjkFromCoeff4_hankel (a : Fin 4 → ℂ) {j k j' k' : Fin 3}
    (h : j.1 + k.1 = j'.1 + k'.1) :
    cjkFromCoeff4 a j k = cjkFromCoeff4 a j' k' := by
  simp [cjkFromCoeff4, h]

/-- Coefficient-weighted shell term. -/
def weightedTerm (a : ℕ → ℂ) (base : ℕ → ℕ → E) : ℕ → ℕ → E :=
  fun j k => cjkFromNatCoeff a j k • base j k

lemma Delta_weightedTerm_shell_factor (a : ℕ → ℂ) (base : ℕ → ℕ → E) (r : ℕ) :
    Delta (weightedTerm a base) r = a (r + 1) • Delta base r := by
  unfold Delta weightedTerm cjkFromNatCoeff
  calc
    (∑ j ∈ Finset.range (r + 1), a (j + (r - j) + 1) • base j (r - j))
        = (∑ j ∈ Finset.range (r + 1), a (r + 1) • base j (r - j)) := by
          apply Finset.sum_congr rfl
          intro j hj
          have hle : j ≤ r := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
          simp [Nat.add_sub_of_le hle]
    _ = a (r + 1) • (∑ j ∈ Finset.range (r + 1), base j (r - j)) := by
          simpa using (Finset.smul_sum (s := Finset.range (r + 1))
            (r := a (r + 1)) (f := fun j => base j (r - j))).symm
    _ = a (r + 1) • Delta base r := by
          simp [Delta]

lemma Delta_weightedTerm_succ_shell_factor (a : ℕ → ℂ) (base : ℕ → ℕ → E) (d : ℕ) :
    Delta (weightedTerm a base) (d + 1) = a (d + 2) • Delta base (d + 1) := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    Delta_weightedTerm_shell_factor (a := a) (base := base) (r := d + 1)

end Step7

section Step8

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The two phase factors in the rotated Hermitian expression. -/
def eMinusIθ (θ : ℝ) : ℂ := Complex.exp (-((θ : ℂ) * Complex.I))
def ePlusIθ (θ : ℝ) : ℂ := Complex.exp ((θ : ℂ) * Complex.I)

/-- Unscaled rotated Hermitian core `e^{-iθ}A + e^{iθ}Aᴴ`. -/
def rotatedCore (A : E →L[ℂ] E) (θ : ℝ) : E →L[ℂ] E :=
  eMinusIθ θ • A + ePlusIθ θ • A.adjoint

/-- The Hermitian part at angle `θ`: `H_θ = (1/2)(e^{-iθ}A + e^{iθ}Aᴴ)`. -/
def Htheta (A : E →L[ℂ] E) (θ : ℝ) : E →L[ℂ] E :=
  ((1 / 2 : ℂ) • rotatedCore A θ)

lemma rotatedCore_apply (A : E →L[ℂ] E) (θ : ℝ) (x : E) :
    rotatedCore A θ x = eMinusIθ θ • A x + ePlusIθ θ • A.adjoint x := by
  simp [rotatedCore]

lemma Htheta_apply (A : E →L[ℂ] E) (θ : ℝ) (x : E) :
    Htheta A θ x = ((1 / 2 : ℂ) • (rotatedCore A θ x)) := by
  simp [Htheta]

lemma two_smul_Htheta_apply (A : E →L[ℂ] E) (θ : ℝ) (x : E) :
    ((2 : ℂ) • Htheta A θ x) = rotatedCore A θ x := by
  simp [Htheta, rotatedCore, smul_smul]

lemma two_smul_eigen_eq
    (A : E →L[ℂ] E) (θ : ℝ) (x : E) (lam : ℂ)
    (hEig : Htheta A θ x = lam • x) :
    ((2 : ℂ) • Htheta A θ x) = (2 * lam) • x := by
  calc
    ((2 : ℂ) • Htheta A θ x) = (2 : ℂ) • (lam • x) := by simp [hEig]
    _ = (2 * lam) • x := by simp [smul_smul]

lemma rotatedCore_eq_two_lambda_smul_of_eigen
    (A : E →L[ℂ] E) (θ : ℝ) (x : E) (lam : ℂ)
    (hEig : Htheta A θ x = lam • x) :
    rotatedCore A θ x = (2 * lam) • x := by
  have hL : ((2 : ℂ) • Htheta A θ x) = rotatedCore A θ x :=
    two_smul_Htheta_apply A θ x
  have hR : ((2 : ℂ) • Htheta A θ x) = (2 * lam) • x :=
    two_smul_eigen_eq A θ x lam hEig
  exact hL.symm.trans hR

lemma aligned_eigenvector_identity_complex
    (A : E →L[ℂ] E) (θStar : ℝ) (x : E) (lam : ℂ)
    (hEig : Htheta A θStar x = lam • x) :
    eMinusIθ θStar • A x + ePlusIθ θStar • A.adjoint x = (2 * lam) • x := by
  have hCore : rotatedCore A θStar x = (2 * lam) • x :=
    rotatedCore_eq_two_lambda_smul_of_eigen A θStar x lam hEig
  simpa [rotatedCore_apply] using hCore

lemma aligned_eigenvector_identity_real
    (A : E →L[ℂ] E) (θStar : ℝ) (x : E) (lambdaMax : ℝ)
    (hEig : Htheta A θStar x = (lambdaMax : ℂ) • x) :
    eMinusIθ θStar • A x + ePlusIθ θStar • A.adjoint x = ((2 * lambdaMax : ℝ) : ℂ) • x := by
  simpa [Complex.ofReal_mul] using
    aligned_eigenvector_identity_complex A θStar x (lambdaMax : ℂ) hEig

lemma aligned_eigenvector_identity_real_with_Astar
    (A Astar : E →L[ℂ] E) (θStar : ℝ) (x : E) (lambdaMax : ℝ)
    (hAstar : Astar = A.adjoint)
    (hEig : Htheta A θStar x = (lambdaMax : ℂ) • x) :
    eMinusIθ θStar • A x + ePlusIθ θStar • Astar x = ((2 * lambdaMax : ℝ) : ℂ) • x := by
  simpa [hAstar] using aligned_eigenvector_identity_real A θStar x lambdaMax hEig

/-- Iterated action of a continuous linear map on vectors. -/
def clmPowAct (T : E →L[ℂ] E) : ℕ → E → E
  | 0, x => x
  | n + 1, x => T (clmPowAct T n x)

lemma aligned_eigenvector_identity_iterate_A
    (A : E →L[ℂ] E) (θStar : ℝ) (x : E) (lam : ℂ)
    (hEig : Htheta A θStar x = lam • x) :
    ∀ n : ℕ,
      eMinusIθ θStar • clmPowAct A (n + 1) x +
        ePlusIθ θStar • clmPowAct A n (A.adjoint x) =
          (2 * lam) • clmPowAct A n x := by
  intro n
  induction n with
  | zero =>
      simpa [clmPowAct] using aligned_eigenvector_identity_complex A θStar x lam hEig
  | succ n ihn =>
      have hmap : A
          (eMinusIθ θStar • clmPowAct A (n + 1) x +
            ePlusIθ θStar • clmPowAct A n (A.adjoint x))
            = A ((2 * lam) • clmPowAct A n x) := congrArg (fun y : E => A y) ihn
      simpa [clmPowAct, map_add, map_smul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hmap

lemma aligned_eigenvector_identity_iterate_Astar
    (A : E →L[ℂ] E) (θStar : ℝ) (x : E) (lam : ℂ)
    (hEig : Htheta A θStar x = lam • x) :
    ∀ n : ℕ,
      eMinusIθ θStar • clmPowAct A.adjoint n (A x) +
        ePlusIθ θStar • clmPowAct A.adjoint (n + 1) x =
          (2 * lam) • clmPowAct A.adjoint n x := by
  intro n
  induction n with
  | zero =>
      simpa [clmPowAct] using aligned_eigenvector_identity_complex A θStar x lam hEig
  | succ n ihn =>
      have hmap : A.adjoint
          (eMinusIθ θStar • clmPowAct A.adjoint n (A x) +
            ePlusIθ θStar • clmPowAct A.adjoint (n + 1) x)
            = A.adjoint ((2 * lam) • clmPowAct A.adjoint n x) := congrArg (fun y : E => A.adjoint y) ihn
      simpa [clmPowAct, map_add, map_smul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hmap

lemma aligned_eigenvector_identity_iterate_A_real
    (A : E →L[ℂ] E) (θStar : ℝ) (x : E) (lambdaMax : ℝ)
    (hEig : Htheta A θStar x = (lambdaMax : ℂ) • x) :
    ∀ n : ℕ,
      eMinusIθ θStar • clmPowAct A (n + 1) x +
        ePlusIθ θStar • clmPowAct A n (A.adjoint x) =
          ((2 * lambdaMax : ℝ) : ℂ) • clmPowAct A n x := by
  simpa [Complex.ofReal_mul] using
    aligned_eigenvector_identity_iterate_A A θStar x (lambdaMax : ℂ) hEig

lemma aligned_eigenvector_identity_iterate_Astar_real
    (A : E →L[ℂ] E) (θStar : ℝ) (x : E) (lambdaMax : ℝ)
    (hEig : Htheta A θStar x = (lambdaMax : ℂ) • x) :
    ∀ n : ℕ,
      eMinusIθ θStar • clmPowAct A.adjoint n (A x) +
        ePlusIθ θStar • clmPowAct A.adjoint (n + 1) x =
          ((2 * lambdaMax : ℝ) : ℂ) • clmPowAct A.adjoint n x := by
  simpa [Complex.ofReal_mul] using
    aligned_eigenvector_identity_iterate_Astar A θStar x (lambdaMax : ℂ) hEig

lemma aligned_eigenvector_identity_iterate_A_real_with_Astar
    (A Astar : E →L[ℂ] E) (θStar : ℝ) (x : E) (lambdaMax : ℝ)
    (hAstar : Astar = A.adjoint)
    (hEig : Htheta A θStar x = (lambdaMax : ℂ) • x) :
    ∀ n : ℕ,
      eMinusIθ θStar • clmPowAct A (n + 1) x +
        ePlusIθ θStar • clmPowAct A n (Astar x) =
          ((2 * lambdaMax : ℝ) : ℂ) • clmPowAct A n x := by
  intro n
  simpa [hAstar] using aligned_eigenvector_identity_iterate_A_real A θStar x lambdaMax hEig n

end Step8

end MyProject
