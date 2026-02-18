import MyProject.MOStep78

noncomputable section

open scoped BigOperators

namespace MyProject

section Step9Split

variable {E : Type*} [AddCommMonoid E]

/-- Index predicate for pure-power words (`j=0` or `k=0`). -/
def IsPurePowerIndex (j k : ℕ) : Prop :=
  j = 0 ∨ k = 0

instance instDecidableIsPurePowerIndex (j k : ℕ) :
    Decidable (IsPurePowerIndex j k) := by
  unfold IsPurePowerIndex
  infer_instance

/-- Pure-power part of a bivariate term family. -/
def purePart (term : ℕ → ℕ → E) : ℕ → ℕ → E :=
  fun j k => if IsPurePowerIndex j k then term j k else 0

/-- Mixed-word part of a bivariate term family. -/
def mixedPart (term : ℕ → ℕ → E) : ℕ → ℕ → E :=
  fun j k => if IsPurePowerIndex j k then 0 else term j k

lemma purePart_add_mixedPart (term : ℕ → ℕ → E) (j k : ℕ) :
    purePart term j k + mixedPart term j k = term j k := by
  by_cases h : IsPurePowerIndex j k <;> simp [purePart, mixedPart, h]

lemma Delta_eq_Delta_purePart_add_Delta_mixedPart
    (term : ℕ → ℕ → E) (r : ℕ) :
    Delta term r = Delta (purePart term) r + Delta (mixedPart term) r := by
  unfold Delta
  calc
    (∑ j ∈ Finset.range (r + 1), term j (r - j))
        = ∑ j ∈ Finset.range (r + 1), (purePart term j (r - j) + mixedPart term j (r - j)) := by
            apply Finset.sum_congr rfl
            intro j hj
            simpa using (purePart_add_mixedPart term j (r - j)).symm
    _ = (∑ j ∈ Finset.range (r + 1), purePart term j (r - j)) +
          (∑ j ∈ Finset.range (r + 1), mixedPart term j (r - j)) := by
            simp [Finset.sum_add_distrib]
    _ = Delta (purePart term) r + Delta (mixedPart term) r := by
            simp [Delta]

lemma w_d_eq_w_d_purePart_add_w_d_mixedPart
    (term : ℕ → ℕ → E) (d : ℕ) :
    w_d term d = w_d (purePart term) d + w_d (mixedPart term) d := by
  unfold w_d
  calc
    (∑ r ∈ Finset.range (d + 1), Delta term r)
        = ∑ r ∈ Finset.range (d + 1),
            (Delta (purePart term) r + Delta (mixedPart term) r) := by
              apply Finset.sum_congr rfl
              intro r hr
              simpa using Delta_eq_Delta_purePart_add_Delta_mixedPart term r
    _ = (∑ r ∈ Finset.range (d + 1), Delta (purePart term) r) +
          (∑ r ∈ Finset.range (d + 1), Delta (mixedPart term) r) := by
            simp [Finset.sum_add_distrib]
    _ = w_d (purePart term) d + w_d (mixedPart term) d := by
            rfl

end Step9Split

section Step9MO

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable (A Astar : E →ₗ[ℂ] E) (x : E)

lemma w_d_purePart_mem_V3_of_shell_hyp
    (term : ℕ → ℕ → E) (d : ℕ)
    (hPure : ∀ r : ℕ, r ≤ d → Delta (purePart term) r ∈ V3 A Astar x) :
    w_d (purePart term) d ∈ V3 A Astar x := by
  unfold w_d
  refine Submodule.sum_mem (V3 A Astar x) ?_
  intro r hr
  exact hPure r (Nat.le_of_lt_succ (Finset.mem_range.mp hr))

lemma w_d_mem_V3_iff_mixedPart_mem_V3_of_pureShells
    (term : ℕ → ℕ → E) (d : ℕ)
    (hPure : ∀ r : ℕ, r ≤ d → Delta (purePart term) r ∈ V3 A Astar x) :
    (w_d term d ∈ V3 A Astar x) ↔
      (w_d (mixedPart term) d ∈ V3 A Astar x) := by
  have hPureWd : w_d (purePart term) d ∈ V3 A Astar x :=
    w_d_purePart_mem_V3_of_shell_hyp (A := A) (Astar := Astar) (x := x) term d hPure
  have hw :
      w_d term d = w_d (purePart term) d + w_d (mixedPart term) d :=
    w_d_eq_w_d_purePart_add_w_d_mixedPart term d
  constructor
  · intro hAll
    have hsum :
        w_d (purePart term) d + w_d (mixedPart term) d ∈ V3 A Astar x := by
      simpa [hw] using hAll
    have hneg : -w_d (purePart term) d ∈ V3 A Astar x :=
      Submodule.neg_mem (V3 A Astar x) hPureWd
    have hmix :
        (w_d (purePart term) d + w_d (mixedPart term) d) + (-w_d (purePart term) d) ∈
          V3 A Astar x :=
      Submodule.add_mem (V3 A Astar x) hsum hneg
    simpa [add_assoc, add_comm, add_left_comm] using hmix
  · intro hMixed
    rw [hw]
    exact Submodule.add_mem (V3 A Astar x) hPureWd hMixed

theorem MO_d_iff_mixedPart_of_pureShells
    [FiniteDimensional ℂ E]
    (term : ℕ → ℕ → E) (d : ℕ)
    (hPure : ∀ r : ℕ, r ≤ d → Delta (purePart term) r ∈ V3 A Astar x) :
    MO_d A Astar x term d ↔ MO_d A Astar x (mixedPart term) d := by
  have hMem :
      (w_d term d ∈ V3 A Astar x) ↔
        (w_d (mixedPart term) d ∈ V3 A Astar x) :=
    w_d_mem_V3_iff_mixedPart_mem_V3_of_pureShells (A := A) (Astar := Astar) (x := x) term d hPure
  constructor
  · intro hMO
    have hwd : w_d term d ∈ V3 A Astar x :=
      (MO_d_iff_w_d_mem_V3 (E := E) A Astar x term d).1 hMO
    have hwdMixed : w_d (mixedPart term) d ∈ V3 A Astar x := hMem.1 hwd
    exact (MO_d_iff_w_d_mem_V3 (E := E) A Astar x (mixedPart term) d).2 hwdMixed
  · intro hMO
    have hwdMixed : w_d (mixedPart term) d ∈ V3 A Astar x :=
      (MO_d_iff_w_d_mem_V3 (E := E) A Astar x (mixedPart term) d).1 hMO
    have hwd : w_d term d ∈ V3 A Astar x := hMem.2 hwdMixed
    exact (MO_d_iff_w_d_mem_V3 (E := E) A Astar x term d).2 hwd

end Step9MO

section Step10Kernel

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable (A Astar : E →ₗ[ℂ] E) (x : E) (term : ℕ → ℕ → E)

/-- Hard-kernel predicate at shell index `r`: mixed-word shell lies in `V3`. -/
def Kernel (r : ℕ) : Prop :=
  Delta (mixedPart term) r ∈ V3 A Astar x

/--
Step-10 closure lemma:
if the pure and mixed pieces of shell `d+1` lie in `V3`, then the induction step closes.
-/
lemma P_step_of_pure_and_kernel
    {d : ℕ}
    (hPd : P A Astar x term d)
    (hPure : Delta (purePart term) (d + 1) ∈ V3 A Astar x)
    (hKernel : Kernel (A := A) (Astar := Astar) (x := x) (term := term) (d + 1)) :
    P A Astar x term (d + 1) := by
  have hDeltaSplit :
      Delta term (d + 1) =
        Delta (purePart term) (d + 1) + Delta (mixedPart term) (d + 1) :=
    Delta_eq_Delta_purePart_add_Delta_mixedPart term (d + 1)
  have hDelta : Delta term (d + 1) ∈ V3 A Astar x := by
    rw [hDeltaSplit]
    exact Submodule.add_mem (V3 A Astar x) hPure hKernel
  exact P_step_of_shell A Astar x term hPd hDelta

end Step10Kernel

section Step11KernelSplit

variable {E : Type*}
variable [AddCommMonoid E]

/-- Left/right placement tag for commutator occurrences inside a mixed word. -/
inductive CommPlacement
  | left
  | right
  | both
deriving DecidableEq

/--
Finite mixed-word shell decomposition data:
`piece` are the atomic mixed-word correction vectors; the three index maps
encode the Step-11 split parameters.
-/
structure KernelSplitData (E : Type*) where
  ι : Type*
  fintype_ι : Fintype ι
  piece : ι → E
  commDeg : ι → ℕ
  wordLen : ι → ℕ
  placement : ι → CommPlacement

attribute [instance] KernelSplitData.fintype_ι

/-- Sum of all mixed-word atomic pieces. -/
def KernelSplitData.total (K : KernelSplitData E) : E :=
  ∑ i : K.ι, K.piece i

/-- Grouped mixed-word sum at fixed commutator degree. -/
def KernelSplitData.byCommDeg (K : KernelSplitData E) (q : ℕ) : E := by
  classical
  exact Finset.sum (Finset.univ.filter (fun i : K.ι => K.commDeg i = q)) (fun i => K.piece i)

/-- Grouped mixed-word sum at fixed commutator degree and word length. -/
def KernelSplitData.byCommDegWordLen (K : KernelSplitData E) (q ℓ : ℕ) : E := by
  classical
  exact Finset.sum
    (Finset.univ.filter (fun i : K.ι => K.commDeg i = q ∧ K.wordLen i = ℓ))
    (fun i => K.piece i)

/-- Grouped mixed-word sum at fixed degree, length, and placement. -/
def KernelSplitData.byCommDegWordLenPlacement
    (K : KernelSplitData E) (q ℓ : ℕ) (p : CommPlacement) : E := by
  classical
  exact Finset.sum
    (Finset.univ.filter
      (fun i : K.ι => K.commDeg i = q ∧ K.wordLen i = ℓ ∧ K.placement i = p))
    (fun i => K.piece i)

end Step11KernelSplit

section Step11KernelTemplate

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/--
Atomic template identity of the form
`⟪ξ, w⟫ = 0` for every `ξ ⟂ V`.
-/
def WordTemplateIdentity (V : Submodule ℂ E) (w : E) : Prop :=
  ∀ ξ, ξ ∈ Vᗮ → inner ℂ ξ w = 0

/-- Family-level template identity package for all mixed-word atoms. -/
def KernelTemplateIdentity (V : Submodule ℂ E) (K : KernelSplitData (E := E)) : Prop :=
  ∀ i : K.ι, WordTemplateIdentity V (K.piece i)

lemma WordTemplateIdentity_of_mem
    (V : Submodule ℂ E) (w : E)
    (hw : w ∈ V) :
    WordTemplateIdentity V w := by
  intro ξ hξ
  exact (inner_eq_zero_symm).1 ((Submodule.mem_orthogonal V ξ).1 hξ w hw)

lemma mem_of_wordTemplateIdentity
    (V : Submodule ℂ E) (w : E)
    (hTemplate : WordTemplateIdentity V w) :
    w ∈ V := by
  have hDouble : w ∈ Vᗮᗮ := by
    rw [Submodule.mem_orthogonal]
    intro ξ hξ
    exact hTemplate ξ hξ
  simpa [Submodule.orthogonal_orthogonal] using hDouble

lemma KernelSplitData.piece_mem_of_template
    (V : Submodule ℂ E) (K : KernelSplitData (E := E))
    (hTemplate : KernelTemplateIdentity V K) :
    ∀ i : K.ι, K.piece i ∈ V := by
  intro i
  exact mem_of_wordTemplateIdentity (V := V) (w := K.piece i) (hTemplate i)

lemma KernelSplitData.total_mem_of_template
    (V : Submodule ℂ E) (K : KernelSplitData (E := E))
    (hTemplate : KernelTemplateIdentity V K) :
    K.total ∈ V := by
  have hPiece : ∀ i : K.ι, K.piece i ∈ V := K.piece_mem_of_template (V := V) hTemplate
  unfold KernelSplitData.total
  exact Submodule.sum_mem V (fun i _ => hPiece i)

lemma KernelSplitData.byCommDeg_mem_of_template
    (V : Submodule ℂ E) (K : KernelSplitData (E := E))
    (hTemplate : KernelTemplateIdentity V K) :
    ∀ q : ℕ, K.byCommDeg q ∈ V := by
  intro q
  classical
  have hPiece : ∀ i : K.ι, K.piece i ∈ V := K.piece_mem_of_template (V := V) hTemplate
  unfold KernelSplitData.byCommDeg
  exact Submodule.sum_mem V (fun i _ => hPiece i)

lemma KernelSplitData.byCommDegWordLen_mem_of_template
    (V : Submodule ℂ E) (K : KernelSplitData (E := E))
    (hTemplate : KernelTemplateIdentity V K) :
    ∀ q ℓ : ℕ, K.byCommDegWordLen q ℓ ∈ V := by
  intro q ℓ
  classical
  have hPiece : ∀ i : K.ι, K.piece i ∈ V := K.piece_mem_of_template (V := V) hTemplate
  unfold KernelSplitData.byCommDegWordLen
  exact Submodule.sum_mem V (fun i _ => hPiece i)

lemma KernelSplitData.byCommDegWordLenPlacement_mem_of_template
    (V : Submodule ℂ E) (K : KernelSplitData (E := E))
    (hTemplate : KernelTemplateIdentity V K) :
    ∀ q ℓ : ℕ, ∀ p : CommPlacement, K.byCommDegWordLenPlacement q ℓ p ∈ V := by
  intro q ℓ p
  classical
  have hPiece : ∀ i : K.ι, K.piece i ∈ V := K.piece_mem_of_template (V := V) hTemplate
  unfold KernelSplitData.byCommDegWordLenPlacement
  exact Submodule.sum_mem V (fun i _ => hPiece i)

end Step11KernelTemplate

section Step11KernelReduction

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
variable (A Astar : E →ₗ[ℂ] E) (x : E) (term : ℕ → ℕ → E) (d : ℕ)

/--
Step-11 reduction theorem:
once a mixed shell is decomposed into finitely many template words, proving
the atomic template identities implies the hard kernel at shell `d+1`.
-/
theorem Kernel_succ_of_templateIdentities
    (K : KernelSplitData (E := E))
    (hShell : Delta (mixedPart term) (d + 1) = K.total)
    (hTemplate : KernelTemplateIdentity (V3 A Astar x) K) :
    Kernel (A := A) (Astar := Astar) (x := x) (term := term) (d + 1) := by
  rw [Kernel, hShell]
  exact K.total_mem_of_template (V := V3 A Astar x) hTemplate

end Step11KernelReduction

section Step11CanonicalReduction

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- Canonical finite index for shell `r`: the `j`-index in `j+k=r`. -/
abbrev ShellIndex (r : ℕ) : Type := Fin (r + 1)

/-- Canonical split datum for shell `r`, using the actual mixed shell terms as atoms. -/
def canonicalKernelSplitData (term : ℕ → ℕ → E) (r : ℕ) : KernelSplitData (E := E) where
  ι := ShellIndex r
  fintype_ι := inferInstance
  piece := fun j => mixedPart term j (r - j)
  commDeg := fun _ => 0
  wordLen := fun _ => r + 1
  placement := fun _ => CommPlacement.both

lemma canonicalKernelSplitData_total_eq_Delta_mixedPart
    (term : ℕ → ℕ → E) (r : ℕ) :
    (canonicalKernelSplitData (E := E) term r).total = Delta (mixedPart term) r := by
  unfold KernelSplitData.total canonicalKernelSplitData Delta
  simpa using
    (Fin.sum_univ_eq_sum_range
      (f := fun j : ℕ => mixedPart term j (r - j)) (n := r + 1))

lemma WordTemplateIdentity_zero (V : Submodule ℂ E) :
    WordTemplateIdentity V (0 : E) := by
  intro ξ hξ
  simp

/--
Canonical Step-11 kernel reduction:
if each atom of the concrete mixed shell at `d+1` satisfies the template identity,
then the hard kernel at `d+1` follows.
-/
theorem Kernel_succ_of_pointwise_mixed_templates
    (A Astar : E →ₗ[ℂ] E) (x : E) (term : ℕ → ℕ → E) (d : ℕ)
    (hTemplatePointwise :
      ∀ j : ShellIndex (d + 1),
        WordTemplateIdentity (V3 A Astar x)
          (mixedPart term j ((d + 1) - j))) :
    Kernel (A := A) (Astar := Astar) (x := x) (term := term) (d + 1) := by
  let K : KernelSplitData (E := E) := canonicalKernelSplitData (E := E) term (d + 1)
  have hShell : Delta (mixedPart term) (d + 1) = K.total := by
    simpa [K] using
      (canonicalKernelSplitData_total_eq_Delta_mixedPart (E := E) term (d + 1)).symm
  have hTemplate : KernelTemplateIdentity (V3 A Astar x) K := by
    intro i
    simpa [K, canonicalKernelSplitData] using hTemplatePointwise i
  exact Kernel_succ_of_templateIdentities
    (A := A) (Astar := Astar) (x := x) (term := term) (d := d) K hShell hTemplate

/--
Step-11 reduced exactly to finite template identities on concrete words:
for each `j=0,...,d+1`, prove `⟪ξ, term j (d+1-j)⟫=0` for all `ξ ⟂ V3`,
restricted to mixed indices (`j ≠ 0` and `d+1-j ≠ 0`).
-/
theorem Kernel_succ_of_pointwise_word_templates
    (A Astar : E →ₗ[ℂ] E) (x : E) (term : ℕ → ℕ → E) (d : ℕ)
    (hTemplatePointwise :
      ∀ j : ShellIndex (d + 1),
        ¬ IsPurePowerIndex (j : ℕ) ((d + 1) - j) →
          WordTemplateIdentity (V3 A Astar x) (term j ((d + 1) - j))) :
    Kernel (A := A) (Astar := Astar) (x := x) (term := term) (d + 1) := by
  have hMixed :
      ∀ j : ShellIndex (d + 1),
        WordTemplateIdentity (V3 A Astar x)
          (mixedPart term j ((d + 1) - j)) := by
    intro j
    by_cases hPure : IsPurePowerIndex (j : ℕ) ((d + 1) - j)
    · simpa [mixedPart, hPure] using
        (WordTemplateIdentity_zero (E := E) (V := V3 A Astar x))
    · simpa [mixedPart, hPure] using hTemplatePointwise j hPure
  exact Kernel_succ_of_pointwise_mixed_templates
    (A := A) (Astar := Astar) (x := x) (term := term) (d := d) hMixed

end Step11CanonicalReduction

section Step9Stage8Bridge

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Stage-8 propagated-identity residual at shell index `r`. -/
def stage8ResidualVector
    (A : E →L[ℂ] E) (x : E) (θ : ℝ) (lambdaMax : ℝ) (r : ℕ) : E :=
  eMinusIθ θ • clmPowAct A (r + 1) x +
    ePlusIθ θ • clmPowAct A r (A.adjoint x) -
    ((2 * lambdaMax : ℝ) : ℂ) • clmPowAct A r x

/-- Concrete term generator whose pure shell at index `r` is `κ r` times the stage-8 residual. -/
def stage8ResidualTerm
    (A : E →L[ℂ] E) (x : E) (θ : ℝ) (lambdaMax : ℝ) (κ : ℕ → ℂ) :
    ℕ → ℕ → E :=
  fun j k =>
    if j = 0 then
      κ k • stage8ResidualVector A x θ lambdaMax k
    else
      0

lemma purePart_stage8ResidualTerm
    (A : E →L[ℂ] E) (x : E) (θ : ℝ) (lambdaMax : ℝ) (κ : ℕ → ℂ) :
    purePart (stage8ResidualTerm A x θ lambdaMax κ) =
      stage8ResidualTerm A x θ lambdaMax κ := by
  funext j k
  by_cases h0 : j = 0 <;>
    simp [purePart, stage8ResidualTerm, IsPurePowerIndex, h0]

lemma Delta_stage8ResidualTerm
    (A : E →L[ℂ] E) (x : E) (θ : ℝ) (lambdaMax : ℝ) (κ : ℕ → ℂ) (r : ℕ) :
    Delta (stage8ResidualTerm A x θ lambdaMax κ) r =
      κ r • stage8ResidualVector A x θ lambdaMax r := by
  unfold Delta
  have hsum :
      (∑ j ∈ Finset.range (r + 1),
        stage8ResidualTerm A x θ lambdaMax κ j (r - j)) =
        stage8ResidualTerm A x θ lambdaMax κ 0 r := by
    refine Finset.sum_eq_single 0 ?_ ?_
    · intro j hj hne
      simp [stage8ResidualTerm, hne]
    · intro h0
      simp at h0
  calc
    (∑ j ∈ Finset.range (r + 1),
        stage8ResidualTerm A x θ lambdaMax κ j (r - j))
        = stage8ResidualTerm A x θ lambdaMax κ 0 r := hsum
    _ = κ r • stage8ResidualVector A x θ lambdaMax r := by
      simp [stage8ResidualTerm]

lemma stage8ResidualVector_eq_zero_of_eig
    (A : E →L[ℂ] E) (x : E) (θ : ℝ) (lambdaMax : ℝ)
    (hEig : Htheta A θ x = (lambdaMax : ℂ) • x) :
    ∀ r : ℕ, stage8ResidualVector A x θ lambdaMax r = 0 := by
  intro r
  have hIter :
      eMinusIθ θ • clmPowAct A (r + 1) x +
        ePlusIθ θ • clmPowAct A r (A.adjoint x) =
          ((2 * lambdaMax : ℝ) : ℂ) • clmPowAct A r x :=
    aligned_eigenvector_identity_iterate_A_real A θ x lambdaMax hEig r
  simp [stage8ResidualVector, hIter]

lemma Delta_stage8ResidualTerm_eq_zero_of_eig
    (A : E →L[ℂ] E) (x : E) (θ : ℝ) (lambdaMax : ℝ) (κ : ℕ → ℂ)
    (hEig : Htheta A θ x = (lambdaMax : ℂ) • x) :
    ∀ r : ℕ, Delta (stage8ResidualTerm A x θ lambdaMax κ) r = 0 := by
  intro r
  have hRes : stage8ResidualVector A x θ lambdaMax r = 0 :=
    stage8ResidualVector_eq_zero_of_eig (A := A) (x := x) (θ := θ) (lambdaMax := lambdaMax) hEig r
  rw [Delta_stage8ResidualTerm (A := A) (x := x) (θ := θ) (lambdaMax := lambdaMax) (κ := κ) r, hRes]
  simp

lemma Delta_purePart_stage8ResidualTerm_eq_zero_of_eig
    (A : E →L[ℂ] E) (x : E) (θ : ℝ) (lambdaMax : ℝ) (κ : ℕ → ℂ)
    (hEig : Htheta A θ x = (lambdaMax : ℂ) • x) :
    ∀ r : ℕ, Delta (purePart (stage8ResidualTerm A x θ lambdaMax κ)) r = 0 := by
  intro r
  rw [purePart_stage8ResidualTerm (A := A) (x := x) (θ := θ) (lambdaMax := lambdaMax) (κ := κ)]
  exact Delta_stage8ResidualTerm_eq_zero_of_eig
    (A := A) (x := x) (θ := θ) (lambdaMax := lambdaMax) (κ := κ) hEig r

end Step9Stage8Bridge

section Step9Concrete

/-- `MO4` data with only mixed-word terms retained. -/
def MO4FiniteData.toMixedData (D : MO4FiniteData) : MO4FiniteData :=
  { D with term := mixedPart D.term }

/-- Pure-power reduction hypothesis up to degree `d` in the `N=4` model. -/
def PurePowerReductionAt4 (D : MO4FiniteData) (d : ℕ) : Prop :=
  ∀ r : ℕ, r ≤ d → Delta (purePart D.term) r ∈ shiftedSpan4 D.x

/-- Degree-uniform pure-power reduction in the `N=4` model. -/
def PurePowerReductionAllAt4 (D : MO4FiniteData) : Prop :=
  ∀ r : ℕ, Delta (purePart D.term) r ∈ shiftedSpan4 D.x

lemma PurePowerReductionAllAt4.to_atDegree
    (D : MO4FiniteData)
    (hPureAll : PurePowerReductionAllAt4 D) (d : ℕ) :
    PurePowerReductionAt4 D d := by
  intro r hr
  exact hPureAll r

theorem MO4_d_iff_mixed_obstruction_of_pureReduction
    (D : MO4FiniteData) (d : ℕ)
    (hPure : PurePowerReductionAt4 D d) :
    MO4_d D d ↔ MO4_d (D.toMixedData) d := by
  have hPureV3 :
      ∀ r : ℕ, r ≤ d → Delta (purePart D.term) r ∈ V3 A4Lin A4AdjLin D.x := by
    intro r hr
    simpa [shiftedSpan4_eq_V3] using hPure r hr
  have hCore :
      MO_d A4Lin A4AdjLin D.x D.term d ↔
        MO_d A4Lin A4AdjLin D.x (mixedPart D.term) d :=
    MO_d_iff_mixedPart_of_pureShells (E := E4MO) (A := A4Lin) (Astar := A4AdjLin) (x := D.x)
      D.term d hPureV3
  have hOrig :
      MO4_d D d ↔ MO_d A4Lin A4AdjLin D.x D.term d :=
    MO4_d_iff_generic D d
  have hMixed :
      MO4_d (D.toMixedData) d ↔
        MO_d A4Lin A4AdjLin D.x (mixedPart D.term) d := by
    simpa [MO4FiniteData.toMixedData] using MO4_d_iff_generic (D := D.toMixedData) d
  exact hOrig.trans (hCore.trans hMixed.symm)

theorem MO4_d_iff_mixed_obstruction_of_pureReductionAll
    (D : MO4FiniteData) (hPureAll : PurePowerReductionAllAt4 D) (d : ℕ) :
    MO4_d D d ↔ MO4_d (D.toMixedData) d :=
  MO4_d_iff_mixed_obstruction_of_pureReduction D d
    (PurePowerReductionAllAt4.to_atDegree D hPureAll d)

theorem MO4_d_of_mixed_and_pureReductionAll
    (D : MO4FiniteData) (hPureAll : PurePowerReductionAllAt4 D) (d : ℕ)
    (hMixed : MO4_d (D.toMixedData) d) :
    MO4_d D d :=
  (MO4_d_iff_mixed_obstruction_of_pureReductionAll D hPureAll d).2 hMixed

theorem MO4_d_toMixed_of_original_and_pureReductionAll
    (D : MO4FiniteData) (hPureAll : PurePowerReductionAllAt4 D) (d : ℕ)
    (hOrig : MO4_d D d) :
    MO4_d (D.toMixedData) d :=
  (MO4_d_iff_mixed_obstruction_of_pureReductionAll D hPureAll d).1 hOrig

lemma MO4Delta_toMixed_zero (D : MO4FiniteData) :
    MO4Delta (D.toMixedData) 0 = 0 := by
  simp [MO4Delta, MO4FiniteData.toMixedData, Delta, mixedPart, IsPurePowerIndex]

lemma MO4Delta_toMixed_one (D : MO4FiniteData) :
    MO4Delta (D.toMixedData) 1 = 0 := by
  unfold MO4Delta Delta
  simp [MO4FiniteData.toMixedData, mixedPart, IsPurePowerIndex, Finset.sum_range_succ]

theorem MO4_d_all_of_pureReductionAll_and_mixed_shell2_tail
    (D : MO4FiniteData)
    (hPureAll : PurePowerReductionAllAt4 D)
    (h2 : MO4Delta (D.toMixedData) 2 ∈ shiftedSpan4 D.x)
    (hTail : ∀ r : ℕ, 3 ≤ r → MO4Delta (D.toMixedData) r ∈ shiftedSpan4 D.x) :
    ∀ d : ℕ, MO4_d D d := by
  have h0 : MO4Delta (D.toMixedData) 0 ∈ shiftedSpan4 D.x := by
    simp [MO4Delta_toMixed_zero D]
  have h1 : MO4Delta (D.toMixedData) 1 ∈ shiftedSpan4 D.x := by
    simp [MO4Delta_toMixed_one D]
  have hMixedAll : ∀ d : ℕ, MO4_d (D.toMixedData) d :=
    MO4_d_all_of_shell_bases_and_tail (D := D.toMixedData) h0 h1 h2 hTail
  intro d
  exact MO4_d_of_mixed_and_pureReductionAll D hPureAll d (hMixedAll d)

/-- Unconditional pure-power reduction in the `N=4` shifted model is false. -/
theorem not_unconditional_purePowerReduction_n4 :
    ¬ (∀ x : E4MO, A4SqLin x ∈ shiftedSpan4 x) :=
  not_forall_A4SqLin_mem_shiftedSpan4

/-- Counterexample term: a single pure-power contribution at `(0,0)`. -/
def termPure00Counter : ℕ → ℕ → E4MO :=
  fun j k => if j = 0 ∧ k = 0 then A4SqLin xBad4 else 0

/-- Concrete `MO4` datum built from `termPure00Counter`. -/
def Dpure00Counter : MO4FiniteData where
  x := xBad4
  v := 0
  thetaStar := 0
  term := termPure00Counter

lemma MO4w_d_Dpure00Counter_zero :
    MO4w_d Dpure00Counter 0 = A4SqLin xBad4 := by
  simp [Dpure00Counter, MO4w_d, w_d, Delta, termPure00Counter]

lemma mixedPart_termPure00Counter_eq_zero :
    mixedPart termPure00Counter = fun _ _ => (0 : E4MO) := by
  funext j k
  by_cases hPure : IsPurePowerIndex j k
  · simp [mixedPart, hPure]
  · have h00 : ¬ (j = 0 ∧ k = 0) := by
      intro hjk
      exact hPure (Or.inl hjk.1)
    simp [mixedPart, hPure, termPure00Counter, h00]

lemma MO4_d_Dpure00Counter_toMixed_zero :
    MO4_d (Dpure00Counter.toMixedData) 0 := by
  have hwd0 : MO4w_d (Dpure00Counter.toMixedData) 0 = 0 := by
    simp [Dpure00Counter, MO4FiniteData.toMixedData, MO4w_d, w_d, Delta,
      mixedPart_termPure00Counter_eq_zero]
  have hmem : MO4w_d (Dpure00Counter.toMixedData) 0 ∈ shiftedSpan4 xBad4 := by
    simp [hwd0]
  simpa [Dpure00Counter, MO4FiniteData.toMixedData] using
    (MO4_d_iff_w_d_mem_shiftedSpan4 (D := Dpure00Counter.toMixedData) 0).2 hmem

lemma not_MO4_d_Dpure00Counter_zero :
    ¬ MO4_d Dpure00Counter 0 := by
  intro hMO
  have hmem : MO4w_d Dpure00Counter 0 ∈ shiftedSpan4 xBad4 :=
    (MO4_d_iff_w_d_mem_shiftedSpan4 (D := Dpure00Counter) 0).1 hMO
  have hnot : MO4w_d Dpure00Counter 0 ∉ shiftedSpan4 xBad4 := by
    simpa [MO4w_d_Dpure00Counter_zero] using A4SqLin_xBad4_not_mem_shiftedSpan4
  exact hnot hmem

/-- Unconditional global split-equivalence is false in the `N=4` shifted model. -/
theorem not_unconditional_MO4_split_equiv :
    ¬ (∀ D : MO4FiniteData, ∀ d : ℕ, MO4_d D d ↔ MO4_d (D.toMixedData) d) := by
  intro hAll
  have hEq : MO4_d Dpure00Counter 0 ↔ MO4_d (Dpure00Counter.toMixedData) 0 :=
    hAll Dpure00Counter 0
  exact not_MO4_d_Dpure00Counter_zero (hEq.mpr MO4_d_Dpure00Counter_toMixed_zero)

/-- Repaired global split-equivalence from a universal pure-power reduction hypothesis. -/
theorem MO4_split_equiv_of_universal_pureReduction
    (hPureAll : ∀ D : MO4FiniteData, ∀ d : ℕ, PurePowerReductionAt4 D d) :
    ∀ D : MO4FiniteData, ∀ d : ℕ, MO4_d D d ↔ MO4_d (D.toMixedData) d := by
  intro D d
  exact MO4_d_iff_mixed_obstruction_of_pureReduction D d (hPureAll D d)

end Step9Concrete

section Step10Step11Concrete

/-- Concrete `N=4` kernel predicate at shell index `r`. -/
def KernelAt4 (D : MO4FiniteData) (r : ℕ) : Prop :=
  MO4Delta (D.toMixedData) r ∈ shiftedSpan4 D.x

/--
Concrete Step-10 closure:
if every successor mixed shell satisfies the kernel predicate, then together with
pure-power reduction the full finite-degree MO family follows.
-/
theorem MO4_d_all_of_pureReductionAll_and_kernelSucc
    (D : MO4FiniteData)
    (hPureAll : PurePowerReductionAllAt4 D)
    (hKernelSucc : ∀ d : ℕ, KernelAt4 D (d + 1)) :
    ∀ d : ℕ, MO4_d D d := by
  have h2 : MO4Delta (D.toMixedData) 2 ∈ shiftedSpan4 D.x := by
    simpa [KernelAt4] using hKernelSucc 1
  have hTail : ∀ r : ℕ, 3 ≤ r → MO4Delta (D.toMixedData) r ∈ shiftedSpan4 D.x := by
    intro r hr
    have hkr : MO4Delta (D.toMixedData) ((r - 1) + 1) ∈ shiftedSpan4 D.x := by
      simpa [KernelAt4] using hKernelSucc (r - 1)
    have hs : (r - 1) + 1 = r := by omega
    simpa [hs] using hkr
  exact MO4_d_all_of_pureReductionAll_and_mixed_shell2_tail D hPureAll h2 hTail

/--
Concrete Step-11 reduction at shell `d+1`:
template identities imply the concrete `N=4` kernel predicate.
-/
theorem KernelAt4_succ_of_templateIdentities
    (D : MO4FiniteData) (d : ℕ)
    (K : KernelSplitData (E := E4MO))
    (hShell : MO4Delta (D.toMixedData) (d + 1) = K.total)
    (hTemplate : KernelTemplateIdentity (shiftedSpan4 D.x) K) :
    KernelAt4 D (d + 1) := by
  rw [KernelAt4, hShell]
  exact K.total_mem_of_template (V := shiftedSpan4 D.x) hTemplate

theorem KernelAt4_succ_of_pointwise_word_templates
    (D : MO4FiniteData) (d : ℕ)
    (hTemplatePointwise :
      ∀ j : ShellIndex (d + 1),
        ¬ IsPurePowerIndex (j : ℕ) ((d + 1) - j) →
          WordTemplateIdentity (shiftedSpan4 D.x) (D.term j ((d + 1) - j))) :
    KernelAt4 D (d + 1) := by
  have hKernel :
      Kernel (A := A4Lin) (Astar := A4AdjLin) (x := D.x) (term := D.term) (d + 1) :=
    Kernel_succ_of_pointwise_word_templates
      (A := A4Lin) (Astar := A4AdjLin) (x := D.x) (term := D.term) (d := d) hTemplatePointwise
  simpa [KernelAt4, Kernel, MO4Delta, MO4FiniteData.toMixedData, shiftedSpan4_eq_V3] using hKernel

theorem KernelAt4_succ_of_pointwise_word_mem
    (D : MO4FiniteData) (d : ℕ)
    (hWordMem :
      ∀ j : ShellIndex (d + 1),
        ¬ IsPurePowerIndex (j : ℕ) ((d + 1) - j) →
          D.term j ((d + 1) - j) ∈ shiftedSpan4 D.x) :
    KernelAt4 D (d + 1) := by
  refine KernelAt4_succ_of_pointwise_word_templates D d ?_
  intro j hMixed
  exact WordTemplateIdentity_of_mem (V := shiftedSpan4 D.x) _ (hWordMem j hMixed)

theorem MO4_d_all_of_pureReductionAll_and_pointwise_word_templates
    (D : MO4FiniteData)
    (hPureAll : PurePowerReductionAllAt4 D)
    (hTemplatePointwise :
      ∀ d : ℕ, ∀ j : ShellIndex (d + 1),
        ¬ IsPurePowerIndex (j : ℕ) ((d + 1) - j) →
          WordTemplateIdentity (shiftedSpan4 D.x) (D.term j ((d + 1) - j))) :
    ∀ d : ℕ, MO4_d D d := by
  have hKernelSucc : ∀ d : ℕ, KernelAt4 D (d + 1) := by
    intro d
    exact KernelAt4_succ_of_pointwise_word_templates D d (hTemplatePointwise d)
  exact MO4_d_all_of_pureReductionAll_and_kernelSucc D hPureAll hKernelSucc

theorem MO4_d_all_of_pureReductionAll_and_pointwise_word_mem
    (D : MO4FiniteData)
    (hPureAll : PurePowerReductionAllAt4 D)
    (hWordMem :
      ∀ d : ℕ, ∀ j : ShellIndex (d + 1),
        ¬ IsPurePowerIndex (j : ℕ) ((d + 1) - j) →
          D.term j ((d + 1) - j) ∈ shiftedSpan4 D.x) :
    ∀ d : ℕ, MO4_d D d := by
  have hKernelSucc : ∀ d : ℕ, KernelAt4 D (d + 1) := by
    intro d
    exact KernelAt4_succ_of_pointwise_word_mem D d (hWordMem d)
  exact MO4_d_all_of_pureReductionAll_and_kernelSucc D hPureAll hKernelSucc

end Step10Step11Concrete

section Step11ExplicitShellSupportAt4

/--
Explicit degree-`≤2` word set at support vector `x`:
pure powers and mixed degree-`2` words used in shell-level bookkeeping.
-/
def wordSetDeg2At4 (x : E4MO) : Set E4MO :=
  ({x, A4Lin x, A4AdjLin x, A4PowAct 2 x, A4AdjPowAct 2 x,
    A4Lin (A4AdjLin x), A4AdjLin (A4Lin x)} : Set E4MO)

/-- Span of explicit degree-`≤2` pure/mixed words at `x`. -/
def wordSpanDeg2At4 (x : E4MO) : Submodule ℂ E4MO :=
  Submodule.span ℂ (wordSetDeg2At4 x)

/--
Strengthened closure package:
in addition to cubic pair closure, include mixed degree-`2` words.
-/
def MixedDegree2ClosureAt4 (x : E4MO) : Prop :=
  A4PowAct 2 x ∈ shiftedSpan4 x ∧
    A4AdjPowAct 2 x ∈ shiftedSpan4 x ∧
      A4Lin (A4AdjLin x) ∈ shiftedSpan4 x ∧
        A4AdjLin (A4Lin x) ∈ shiftedSpan4 x

lemma wordSpanDeg2At4_le_shiftedSpan4
    (x : E4MO) (hClose : MixedDegree2ClosureAt4 x) :
    wordSpanDeg2At4 x ≤ shiftedSpan4 x := by
  rcases hClose with ⟨hA2, hAstar2, hAAstar, hAstarA⟩
  refine Submodule.span_le.mpr ?_
  intro y hy
  have hy' :
      y = x ∨ y = A4Lin x ∨ y = A4AdjLin x ∨ y = A4PowAct 2 x ∨
        y = A4AdjPowAct 2 x ∨ y = A4Lin (A4AdjLin x) ∨ y = A4AdjLin (A4Lin x) := by
    simpa [wordSetDeg2At4, Set.mem_insert_iff] using hy
  rcases hy' with rfl | hy'
  · exact Submodule.subset_span (by simp [Set.mem_insert_iff])
  · rcases hy' with rfl | hy'
    · exact Submodule.subset_span (by simp [Set.mem_insert_iff])
    · rcases hy' with rfl | hy'
      · exact Submodule.subset_span (by simp [Set.mem_insert_iff])
      · rcases hy' with rfl | hy'
        · exact hA2
        · rcases hy' with rfl | hy'
          · exact hAstar2
          · rcases hy' with rfl | rfl
            · exact hAAstar
            · exact hAstarA

/--
Explicit shell-support hypothesis:
every mixed shell atom lies in the span of the listed degree-`≤2` words.
-/
def ShellMixedAtomsInWordSpanDeg2At4 (D : MO4FiniteData) : Prop :=
  ∀ d : ℕ, ∀ j : ShellIndex (d + 1),
    ¬ IsPurePowerIndex (j : ℕ) ((d + 1) - j) →
      D.term j ((d + 1) - j) ∈ wordSpanDeg2At4 D.x

lemma pointwise_word_mem_of_shellMixedAtomsInWordSpanDeg2At4
    (D : MO4FiniteData)
    (hClose : MixedDegree2ClosureAt4 D.x)
    (hSupport : ShellMixedAtomsInWordSpanDeg2At4 D) :
    ∀ d : ℕ, ∀ j : ShellIndex (d + 1),
      ¬ IsPurePowerIndex (j : ℕ) ((d + 1) - j) →
        D.term j ((d + 1) - j) ∈ shiftedSpan4 D.x := by
  intro d j hMixed
  exact (wordSpanDeg2At4_le_shiftedSpan4 D.x hClose) (hSupport d j hMixed)

/--
Alternative explicit model assumption:
all mixed shell atoms are zero (pure-power-only shell model).
-/
def ShellMixedAtomsZeroAt4 (D : MO4FiniteData) : Prop :=
  ∀ d : ℕ, ∀ j : ShellIndex (d + 1),
    ¬ IsPurePowerIndex (j : ℕ) ((d + 1) - j) →
      D.term j ((d + 1) - j) = 0

theorem MO4_d_all_of_pureReductionAll_and_mixedAtomsZero
    (D : MO4FiniteData)
    (hPureAll : PurePowerReductionAllAt4 D)
    (hZero : ShellMixedAtomsZeroAt4 D) :
    ∀ d : ℕ, MO4_d D d := by
  apply MO4_d_all_of_pureReductionAll_and_pointwise_word_mem D hPureAll
  intro d j hMixed
  have hz : D.term j ((d + 1) - j) = 0 := hZero d j hMixed
  simp [hz]

/--
Concrete closure theorem with explicit shell support:
pure-power reduction plus mixed degree-`2` closure plus explicit shell-word support
implies full finite-degree MO.
-/
theorem MO4_d_all_of_pureReductionAll_and_deg2WordSupport
    (D : MO4FiniteData)
    (hPureAll : PurePowerReductionAllAt4 D)
    (hClose : MixedDegree2ClosureAt4 D.x)
    (hSupport : ShellMixedAtomsInWordSpanDeg2At4 D) :
    ∀ d : ℕ, MO4_d D d := by
  apply MO4_d_all_of_pureReductionAll_and_pointwise_word_mem D hPureAll
  exact pointwise_word_mem_of_shellMixedAtomsInWordSpanDeg2At4 D hClose hSupport

end Step11ExplicitShellSupportAt4

section Step9Stage8BridgeConcrete

abbrev A4CLM : E4MO →L[ℂ] E4MO := A4Lin.toContinuousLinearMap

def PureShellProfileAt4 (D : MO4FiniteData) (lambdaMax : ℝ) (κ : ℕ → ℂ) : Prop :=
  ∀ r : ℕ,
    Delta (purePart D.term) r =
      κ r • stage8ResidualVector A4CLM D.x D.thetaStar lambdaMax r

theorem PurePowerReductionAllAt4_of_pureShellProfile
    (D : MO4FiniteData) (lambdaMax : ℝ) (κ : ℕ → ℂ)
    (hProfile : PureShellProfileAt4 D lambdaMax κ)
    (hEig : Htheta A4CLM D.thetaStar D.x = (lambdaMax : ℂ) • D.x) :
    PurePowerReductionAllAt4 D := by
  intro r
  rw [hProfile r]
  have hRes : stage8ResidualVector A4CLM D.x D.thetaStar lambdaMax r = 0 :=
    stage8ResidualVector_eq_zero_of_eig
      (A := A4CLM) (x := D.x) (θ := D.thetaStar) (lambdaMax := lambdaMax) hEig r
  simp [hRes]

/--
Concrete bridge for `N=4`: if the term generator is the stage-8 propagated residual family,
then pure-power reduction holds at all degrees.
-/
theorem PurePowerReductionAllAt4_of_stage8ResidualTerm
    (D : MO4FiniteData) (lambdaMax : ℝ) (κ : ℕ → ℂ)
    (hterm : D.term = stage8ResidualTerm A4CLM D.x D.thetaStar lambdaMax κ)
    (hEig : Htheta A4CLM D.thetaStar D.x = (lambdaMax : ℂ) • D.x) :
    PurePowerReductionAllAt4 D := by
  intro r
  have hzero : Delta (purePart D.term) r = 0 := by
    rw [hterm]
    exact Delta_purePart_stage8ResidualTerm_eq_zero_of_eig
      (A := A4CLM) (x := D.x) (θ := D.thetaStar) (lambdaMax := lambdaMax) (κ := κ) hEig r
  simp [hzero]

lemma WordTemplateIdentity_stage8ResidualTerm_of_mixed_index
    (x : E4MO) (thetaStar : ℝ) (lambdaMax : ℝ) (κ : ℕ → ℂ) (d : ℕ)
    (j : ShellIndex (d + 1))
    (hMixed : ¬ IsPurePowerIndex (j : ℕ) ((d + 1) - j)) :
    WordTemplateIdentity (shiftedSpan4 x)
      (stage8ResidualTerm A4CLM x thetaStar lambdaMax κ j ((d + 1) - j)) := by
  have hj0 : (j : ℕ) ≠ 0 := by
    intro hj
    exact hMixed (Or.inl hj)
  simpa [stage8ResidualTerm, hj0] using
    (WordTemplateIdentity_zero (E := E4MO) (V := shiftedSpan4 x))

theorem KernelAt4_succ_of_stage8ResidualTerm
    (D : MO4FiniteData) (d : ℕ) (lambdaMax : ℝ) (κ : ℕ → ℂ)
    (hterm : D.term = stage8ResidualTerm A4CLM D.x D.thetaStar lambdaMax κ) :
    KernelAt4 D (d + 1) := by
  refine KernelAt4_succ_of_pointwise_word_templates D d ?_
  intro j hMixed
  simpa [hterm] using
    (WordTemplateIdentity_stage8ResidualTerm_of_mixed_index
      (x := D.x) (thetaStar := D.thetaStar) (lambdaMax := lambdaMax) (κ := κ) (d := d) j hMixed)

theorem MO4_d_all_of_stage8ResidualTerm
    (D : MO4FiniteData) (lambdaMax : ℝ) (κ : ℕ → ℂ)
    (hterm : D.term = stage8ResidualTerm A4CLM D.x D.thetaStar lambdaMax κ)
    (hEig : Htheta A4CLM D.thetaStar D.x = (lambdaMax : ℂ) • D.x) :
    ∀ d : ℕ, MO4_d D d := by
  have hPureAll : PurePowerReductionAllAt4 D :=
    PurePowerReductionAllAt4_of_stage8ResidualTerm D lambdaMax κ hterm hEig
  have hTemplatePointwise :
      ∀ d : ℕ, ∀ j : ShellIndex (d + 1),
        ¬ IsPurePowerIndex (j : ℕ) ((d + 1) - j) →
          WordTemplateIdentity (shiftedSpan4 D.x) (D.term j ((d + 1) - j)) := by
    intro d j hMixed
    simpa [hterm] using
      (WordTemplateIdentity_stage8ResidualTerm_of_mixed_index
        (x := D.x) (thetaStar := D.thetaStar) (lambdaMax := lambdaMax) (κ := κ) (d := d) j hMixed)
  exact MO4_d_all_of_pureReductionAll_and_pointwise_word_templates D hPureAll hTemplatePointwise

theorem MO4_d_all_of_pureShellProfile_and_pointwise_word_mem
    (D : MO4FiniteData) (lambdaMax : ℝ) (κ : ℕ → ℂ)
    (hProfile : PureShellProfileAt4 D lambdaMax κ)
    (hEig : Htheta A4CLM D.thetaStar D.x = (lambdaMax : ℂ) • D.x)
    (hWordMem :
      ∀ d : ℕ, ∀ j : ShellIndex (d + 1),
        ¬ IsPurePowerIndex (j : ℕ) ((d + 1) - j) →
          D.term j ((d + 1) - j) ∈ shiftedSpan4 D.x) :
    ∀ d : ℕ, MO4_d D d := by
  have hPureAll : PurePowerReductionAllAt4 D :=
    PurePowerReductionAllAt4_of_pureShellProfile D lambdaMax κ hProfile hEig
  exact MO4_d_all_of_pureReductionAll_and_pointwise_word_mem D hPureAll hWordMem

def MORemainingBridgeAt4 (D : MO4FiniteData) (lambdaMax : ℝ) (κ : ℕ → ℂ) : Prop :=
  PureShellProfileAt4 D lambdaMax κ ∧
    (∀ d : ℕ, ∀ j : ShellIndex (d + 1),
      ¬ IsPurePowerIndex (j : ℕ) ((d + 1) - j) →
        D.term j ((d + 1) - j) ∈ shiftedSpan4 D.x)

theorem MO4_d_all_of_remainingBridge
    (D : MO4FiniteData) (lambdaMax : ℝ) (κ : ℕ → ℂ)
    (hEig : Htheta A4CLM D.thetaStar D.x = (lambdaMax : ℂ) • D.x)
    (hBridge : MORemainingBridgeAt4 D lambdaMax κ) :
    ∀ d : ℕ, MO4_d D d := by
  exact MO4_d_all_of_pureShellProfile_and_pointwise_word_mem
    D lambdaMax κ hBridge.1 hEig hBridge.2

theorem MORemainingBridgeAt4_of_stage8ResidualTerm
    (D : MO4FiniteData) (lambdaMax : ℝ) (κ : ℕ → ℂ)
    (hterm : D.term = stage8ResidualTerm A4CLM D.x D.thetaStar lambdaMax κ) :
    MORemainingBridgeAt4 D lambdaMax κ := by
  refine ⟨?_, ?_⟩
  · intro r
    rw [hterm, purePart_stage8ResidualTerm (A := A4CLM) (x := D.x)
      (θ := D.thetaStar) (lambdaMax := lambdaMax) (κ := κ)]
    exact Delta_stage8ResidualTerm
      (A := A4CLM) (x := D.x) (θ := D.thetaStar) (lambdaMax := lambdaMax) (κ := κ) r
  · intro d j hMixed
    have hj0 : (j : ℕ) ≠ 0 := by
      intro hj
      exact hMixed (Or.inl hj)
    rw [hterm]
    simp [stage8ResidualTerm, hj0]

theorem MO4_d_all_of_stage8ResidualTerm_via_remainingBridge
    (D : MO4FiniteData) (lambdaMax : ℝ) (κ : ℕ → ℂ)
    (hterm : D.term = stage8ResidualTerm A4CLM D.x D.thetaStar lambdaMax κ)
    (hEig : Htheta A4CLM D.thetaStar D.x = (lambdaMax : ℂ) • D.x) :
    ∀ d : ℕ, MO4_d D d := by
  exact MO4_d_all_of_remainingBridge D lambdaMax κ hEig
    (MORemainingBridgeAt4_of_stage8ResidualTerm D lambdaMax κ hterm)

end Step9Stage8BridgeConcrete

end MyProject
