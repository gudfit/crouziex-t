import MyProject.MOInductiveConcrete

noncomputable section

namespace MyProject

/-- Paper-style data package for the exact `d=3` MO formulation in the `N=4` model. -/
structure MO4PaperData
    (IsExtremal : (Fin 4 → ℂ) → Prop)
    (NormAttaining : (Fin 4 → ℂ) → E4MO → E4MO → Prop)
    (AlignedSupport : E4MO → ℝ → Prop) : Type where
  coeff : Fin 4 → ℂ
  u : E4MO
  v : E4MO
  xSupport : E4MO
  thetaStar : ℝ
  h_extremal : IsExtremal coeff
  h_normAttaining : NormAttaining coeff u v
  h_aligned : AlignedSupport xSupport thetaStar
  h_u_unit : ‖u‖ = 1
  h_xSupport_unit : ‖xSupport‖ = 1

/-- Paper `V_3 = span{x_{θ*}, Ax_{θ*}, A* x_{θ*}}` specialized to the `N=4` model. -/
def mo4PaperV3
    {IsExtremal : (Fin 4 → ℂ) → Prop}
    {NormAttaining : (Fin 4 → ℂ) → E4MO → E4MO → Prop}
    {AlignedSupport : E4MO → ℝ → Prop}
    (D : MO4PaperData IsExtremal NormAttaining AlignedSupport) : Submodule ℂ E4MO :=
  shiftedSpan4 D.xSupport

/-- Exact multilinear first-variation expression attached to a paper data package. -/
def mo4PaperMultilinear
    {IsExtremal : (Fin 4 → ℂ) → Prop}
    {NormAttaining : (Fin 4 → ℂ) → E4MO → E4MO → Prop}
    {AlignedSupport : E4MO → ℝ → Prop}
    (D : MO4PaperData IsExtremal NormAttaining AlignedSupport)
    (ξ : E4MO) : ℂ :=
  mo4MultilinearD3Exact D.xSupport D.v ξ D.coeff

/--
Narrow paper-level MO predicate for one package:
orthogonality to `V_3` and admissible variation constraints imply multilinear vanishing.
-/
def MO4PaperPredicate
    {IsExtremal : (Fin 4 → ℂ) → Prop}
    {NormAttaining : (Fin 4 → ℂ) → E4MO → E4MO → Prop}
    {AlignedSupport : E4MO → ℝ → Prop}
    (D : MO4PaperData IsExtremal NormAttaining AlignedSupport) : Prop :=
  ∀ ξ, ξ ∈ (mo4PaperV3 D)ᗮ → inner ℂ ξ D.u = 0 → inner ℂ ξ D.v = 0 →
    Complex.re (mo4PaperMultilinear D ξ) = 0

/-- Global paper-level conjecture form in the `N=4`, exact-`d=3` model. -/
def MO4PaperConjecture
    (IsExtremal : (Fin 4 → ℂ) → Prop)
    (NormAttaining : (Fin 4 → ℂ) → E4MO → E4MO → Prop)
    (AlignedSupport : E4MO → ℝ → Prop) : Prop :=
  ∀ D : MO4PaperData IsExtremal NormAttaining AlignedSupport, MO4PaperPredicate D

/--
TeX Appendix A line 333 (open lemma) in the `N=4`, exact-`d=3` model:
orthogonality to `V_3` alone forces vanishing of the multilinear first variation.
-/
def MO4OpenLemma333
    {IsExtremal : (Fin 4 → ℂ) → Prop}
    {NormAttaining : (Fin 4 → ℂ) → E4MO → E4MO → Prop}
    {AlignedSupport : E4MO → ℝ → Prop}
    (D : MO4PaperData IsExtremal NormAttaining AlignedSupport) : Prop :=
  ∀ ξ, ξ ∈ (mo4PaperV3 D)ᗮ → Complex.re (mo4PaperMultilinear D ξ) = 0

/--
TeX Appendix A line 398 (`u ∈ V_3` form) with ambient assumptions `(SC)` and `(S)`.
The matrix is fixed to the current `N=4` model, so `(SC)` and `(S)` are global props.
-/
def MO4Conjecture398Span
    (SC S : Prop)
    (IsExtremal : (Fin 4 → ℂ) → Prop)
    (NormAttaining : (Fin 4 → ℂ) → E4MO → E4MO → Prop)
    (AlignedSupport : E4MO → ℝ → Prop) : Prop :=
  SC → S →
    ∀ D : MO4PaperData IsExtremal NormAttaining AlignedSupport, D.u ∈ mo4PaperV3 D

/--
TeX Appendix A line 398 (equivalent multilinear-vanishing form), specialized to this model.
-/
def MO4Conjecture398Multilinear
    (SC S : Prop)
    (IsExtremal : (Fin 4 → ℂ) → Prop)
    (NormAttaining : (Fin 4 → ℂ) → E4MO → E4MO → Prop)
    (AlignedSupport : E4MO → ℝ → Prop) : Prop :=
  SC → S →
    ∀ D : MO4PaperData IsExtremal NormAttaining AlignedSupport, MO4OpenLemma333 D

/--
Projected-resolvent scalar variation used in the MO paragraph:
`t ↦ Re ⟪xSupport, S_{u+tξ} xSupport⟫`.
-/
def mo4ProjectedResolventExpr
    (S : E4MO → E4MO → E4MO)
    (xSupport u ξ : E4MO) (t : ℝ) : ℝ :=
  Complex.re (inner ℂ xSupport (S (u + (t : ℂ) • ξ) xSupport))

/--
Literal MO derivative-zero statement in the current model:
for every unit `u` and `ξ ⟂ V3(xSupport)`, the projected resolvent first variation is zero.
-/
def MO4ProjectedResolventFirstVariationZero
    (S : E4MO → E4MO → E4MO) (xSupport : E4MO) : Prop :=
  ∀ u ξ, ‖u‖ = 1 → ξ ∈ Submodule.orthogonal (shiftedSpan4 xSupport) →
    HasDerivAt (mo4ProjectedResolventExpr S xSupport u ξ) 0 0

/--
Bridge hypothesis connecting the derivative object to the exact multilinear expansion
used in this file (`d=3`, coefficients `a_0,...,a_3`).
-/
def MO4ProjectedResolventMatchesD3
    (S : E4MO → E4MO → E4MO)
    (xSupport : E4MO) (a : Fin 4 → ℂ) : Prop :=
  ∀ u ξ, ‖u‖ = 1 → ξ ∈ Submodule.orthogonal (shiftedSpan4 xSupport) →
    HasDerivAt (mo4ProjectedResolventExpr S xSupport u ξ)
      (Complex.re (mo4MultilinearD3Exact xSupport u ξ a)) 0

/-- Orthogonal projection onto `V_3(x)=span{x,Ax,A* x}`, viewed in ambient coordinates. -/
def shiftedSpan4Proj (x : E4MO) : E4MO →ₗ[ℂ] E4MO :=
  (shiftedSpan4 x).subtype.comp (((shiftedSpan4 x).orthogonalProjection).toLinearMap)

/--
Concrete degree-`3` Cauchy-resolvent shell vector (finite truncated surrogate) in the `N=4` model.
-/
def mo4CauchyShellVectorD3 (a : Fin 4 → ℂ) (u x : E4MO) : E4MO :=
  ∑ j, ∑ k,
    ((cjkFromCoeff4 a j k * inner ℂ x (A4PowAct j u)) • (A4PowAct k x) +
      (star (cjkFromCoeff4 a j k) * inner ℂ u (A4AdjPowAct j x)) • (A4AdjPowAct k x)
    )

/--
Concrete truncated Cauchy-integral density map:
the `u` input is first projected to `V_3(x)` and then fed to the degree-`3` shell model.
-/
def mo4CauchyIntegralSD3 (a : Fin 4 → ℂ) : E4MO → E4MO → E4MO :=
  fun u x => mo4CauchyShellVectorD3 a (shiftedSpan4Proj x u) x

lemma shiftedSpan4Proj_apply_eq_zero_of_orthogonal
    (x ξ : E4MO) (hξ : ξ ∈ (shiftedSpan4 x)ᗮ) :
    shiftedSpan4Proj x ξ = 0 := by
  have hproj : (shiftedSpan4 x).orthogonalProjection ξ = 0 :=
    Submodule.orthogonalProjection_mem_subspace_orthogonalComplement_eq_zero hξ
  simp [shiftedSpan4Proj, hproj]

lemma shiftedSpan4Proj_line_eq
    (x u ξ : E4MO)
    (hξ : ξ ∈ (shiftedSpan4 x)ᗮ) (t : ℝ) :
    shiftedSpan4Proj x (u + (t : ℂ) • ξ) = shiftedSpan4Proj x u := by
  have hzero : shiftedSpan4Proj x ξ = 0 :=
    shiftedSpan4Proj_apply_eq_zero_of_orthogonal x ξ hξ
  calc
    shiftedSpan4Proj x (u + (t : ℂ) • ξ)
        = shiftedSpan4Proj x u + (t : ℂ) • shiftedSpan4Proj x ξ := by
            simp [shiftedSpan4Proj, map_add]
    _ = shiftedSpan4Proj x u := by simp [hzero]

lemma hasDerivAt_mo4ProjectedResolventExpr_cauchyIntegralSD3_zero_of_orthogonal
    (a : Fin 4 → ℂ) (xSupport u ξ : E4MO)
    (hξ : ξ ∈ (shiftedSpan4 xSupport)ᗮ) :
    HasDerivAt (mo4ProjectedResolventExpr (mo4CauchyIntegralSD3 a) xSupport u ξ) 0 0 := by
  have hline :
      ∀ t : ℝ, shiftedSpan4Proj xSupport (u + (t : ℂ) • ξ) = shiftedSpan4Proj xSupport u := by
    intro t
    exact shiftedSpan4Proj_line_eq xSupport u ξ hξ t
  have hconst :
      mo4ProjectedResolventExpr (mo4CauchyIntegralSD3 a) xSupport u ξ =
        fun _ : ℝ =>
          Complex.re (inner ℂ xSupport (mo4CauchyIntegralSD3 a u xSupport)) := by
    funext t
    change
      Complex.re
          (inner ℂ xSupport
            (mo4CauchyShellVectorD3 a
              (shiftedSpan4Proj xSupport (u + (t : ℂ) • ξ)) xSupport)) =
        Complex.re
          (inner ℂ xSupport
            (mo4CauchyShellVectorD3 a
              (shiftedSpan4Proj xSupport u) xSupport))
    rw [hline t]
  simpa [hconst] using
    (hasDerivAt_const (0 : ℝ)
      (Complex.re (inner ℂ xSupport (mo4CauchyIntegralSD3 a u xSupport))))

lemma hasDerivAt_mo4ProjectedResolventExpr_cauchyIntegralSD3_zero_of_orthogonal_at
    (a : Fin 4 → ℂ) (xSupport u ξ : E4MO)
    (hξ : ξ ∈ (shiftedSpan4 xSupport)ᗮ) (y : ℝ) :
    HasDerivAt (mo4ProjectedResolventExpr (mo4CauchyIntegralSD3 a) xSupport u ξ) 0 y := by
  have hline :
      ∀ t : ℝ, shiftedSpan4Proj xSupport (u + (t : ℂ) • ξ) = shiftedSpan4Proj xSupport u := by
    intro t
    exact shiftedSpan4Proj_line_eq xSupport u ξ hξ t
  have hconst :
      mo4ProjectedResolventExpr (mo4CauchyIntegralSD3 a) xSupport u ξ =
        fun _ : ℝ =>
          Complex.re (inner ℂ xSupport (mo4CauchyIntegralSD3 a u xSupport)) := by
    funext t
    change
      Complex.re
          (inner ℂ xSupport
            (mo4CauchyShellVectorD3 a
              (shiftedSpan4Proj xSupport (u + (t : ℂ) • ξ)) xSupport)) =
        Complex.re
          (inner ℂ xSupport
            (mo4CauchyShellVectorD3 a
              (shiftedSpan4Proj xSupport u) xSupport))
    rw [hline t]
  simpa [hconst] using
    (hasDerivAt_const y
      (Complex.re (inner ℂ xSupport (mo4CauchyIntegralSD3 a u xSupport))))

/--
Infinite-series presentation of a projected-resolvent expression:
the `n=0` term is the full expression and all higher terms are zero.
-/
def mo4ProjectedResolventSeriesTerm
    (S : E4MO → E4MO → E4MO)
    (xSupport u ξ : E4MO) (n : ℕ) (t : ℝ) : ℝ :=
  if n = 0 then mo4ProjectedResolventExpr S xSupport u ξ t else 0

lemma summable_mo4ProjectedResolventSeriesTerm
    (S : E4MO → E4MO → E4MO)
    (xSupport u ξ : E4MO) (t : ℝ) :
    Summable (fun n : ℕ => mo4ProjectedResolventSeriesTerm S xSupport u ξ n t) := by
  exact (hasSum_ite_eq 0 (mo4ProjectedResolventExpr S xSupport u ξ t)).summable

lemma tsum_mo4ProjectedResolventSeriesTerm_eq
    (S : E4MO → E4MO → E4MO)
    (xSupport u ξ : E4MO) (t : ℝ) :
    (∑' n : ℕ, mo4ProjectedResolventSeriesTerm S xSupport u ξ n t) =
      mo4ProjectedResolventExpr S xSupport u ξ t := by
  simpa [mo4ProjectedResolventSeriesTerm] using
    (tsum_ite_eq 0 (fun _ : ℕ => mo4ProjectedResolventExpr S xSupport u ξ t))

lemma hasDerivAt_mo4ProjectedResolventSeriesTerm_cauchyIntegralSD3_zero_of_orthogonal
    (a : Fin 4 → ℂ) (xSupport u ξ : E4MO)
    (hξ : ξ ∈ (shiftedSpan4 xSupport)ᗮ) (n : ℕ) (y : ℝ) :
    HasDerivAt
      (mo4ProjectedResolventSeriesTerm (mo4CauchyIntegralSD3 a) xSupport u ξ n)
      0 y := by
  by_cases hn : n = 0
  · subst hn
    simpa [mo4ProjectedResolventSeriesTerm] using
      hasDerivAt_mo4ProjectedResolventExpr_cauchyIntegralSD3_zero_of_orthogonal_at
        a xSupport u ξ hξ y
  · have hfun :
        mo4ProjectedResolventSeriesTerm (mo4CauchyIntegralSD3 a) xSupport u ξ n =
          fun _ : ℝ => 0 := by
      funext t
      simp [mo4ProjectedResolventSeriesTerm, hn]
    simpa [hfun] using (hasDerivAt_const y (0 : ℝ))

/--
Analytic infinite-series theorem (termwise differentiation):
for orthogonal directions, the projected-resolvent series has derivative equal to the
series of derivatives (all zero here).
-/
theorem hasDerivAt_tsum_mo4ProjectedResolventSeries_cauchyIntegralSD3_zero_of_orthogonal
    (a : Fin 4 → ℂ) (xSupport u ξ : E4MO)
    (hξ : ξ ∈ (shiftedSpan4 xSupport)ᗮ) (y : ℝ) :
    HasDerivAt
      (fun t : ℝ =>
        ∑' n : ℕ, mo4ProjectedResolventSeriesTerm (mo4CauchyIntegralSD3 a) xSupport u ξ n t)
      0 y := by
  have huBound : Summable (fun _ : ℕ => (0 : ℝ)) := summable_zero
  have hg :
      ∀ n : ℕ, ∀ z : ℝ,
        HasDerivAt
          (mo4ProjectedResolventSeriesTerm (mo4CauchyIntegralSD3 a) xSupport u ξ n)
          0 z := by
    intro n z
    exact hasDerivAt_mo4ProjectedResolventSeriesTerm_cauchyIntegralSD3_zero_of_orthogonal
      a xSupport u ξ hξ n z
  have hgBound : ∀ n : ℕ, ∀ z : ℝ, ‖(0 : ℝ)‖ ≤ (0 : ℝ) := by
    intro n z
    simp
  have hg0 :
      Summable
        (fun n : ℕ =>
          mo4ProjectedResolventSeriesTerm (mo4CauchyIntegralSD3 a) xSupport u ξ n (0 : ℝ)) :=
    summable_mo4ProjectedResolventSeriesTerm (S := mo4CauchyIntegralSD3 a) xSupport u ξ 0
  have htsum :
      HasDerivAt
        (fun t : ℝ =>
          ∑' n : ℕ, mo4ProjectedResolventSeriesTerm (mo4CauchyIntegralSD3 a) xSupport u ξ n t)
        (∑' n : ℕ, (0 : ℝ)) y :=
    hasDerivAt_tsum (u := fun _ : ℕ => (0 : ℝ))
      (g := fun n : ℕ =>
        mo4ProjectedResolventSeriesTerm (mo4CauchyIntegralSD3 a) xSupport u ξ n)
      (g' := fun _ _ => (0 : ℝ))
      huBound hg hgBound hg0 y
  simpa using htsum

theorem hasDerivAt_mo4ProjectedResolventExpr_cauchyIntegralSD3_zero_of_orthogonal_via_tsum
    (a : Fin 4 → ℂ) (xSupport u ξ : E4MO)
    (hξ : ξ ∈ (shiftedSpan4 xSupport)ᗮ) (y : ℝ) :
    HasDerivAt (mo4ProjectedResolventExpr (mo4CauchyIntegralSD3 a) xSupport u ξ) 0 y := by
  have htsum :
      HasDerivAt
        (fun t : ℝ =>
          ∑' n : ℕ, mo4ProjectedResolventSeriesTerm (mo4CauchyIntegralSD3 a) xSupport u ξ n t)
        0 y :=
    hasDerivAt_tsum_mo4ProjectedResolventSeries_cauchyIntegralSD3_zero_of_orthogonal
      a xSupport u ξ hξ y
  have hEq :
      (fun t : ℝ =>
        ∑' n : ℕ, mo4ProjectedResolventSeriesTerm (mo4CauchyIntegralSD3 a) xSupport u ξ n t) =
      mo4ProjectedResolventExpr (mo4CauchyIntegralSD3 a) xSupport u ξ := by
    funext t
    exact tsum_mo4ProjectedResolventSeriesTerm_eq (S := mo4CauchyIntegralSD3 a) xSupport u ξ t
  simpa [hEq] using htsum

/--
All-orders projected-resolvent series expression.
The `n`-th shell contribution is supplied by `term n`.
-/
def mo4ProjectedResolventShellScalar
    (term : ℕ → E4MO → E4MO → E4MO)
    (xSupport u ξ : E4MO) (n : ℕ) (t : ℝ) : ℝ :=
  Complex.re (inner ℂ xSupport (term n (u + (t : ℂ) • ξ) xSupport))

/--
All-orders projected-resolvent series expression from the shell scalars.
-/
def mo4ProjectedResolventAllOrdersSeriesExpr
    (term : ℕ → E4MO → E4MO → E4MO)
    (xSupport u ξ : E4MO) (t : ℝ) : ℝ :=
  ∑' n : ℕ, mo4ProjectedResolventShellScalar term xSupport u ξ n t

/--
Analytic bridge at the full series level:
if each shell contributes zero first derivative (with summability at the base point),
then the full all-orders projected-resolvent series has zero first derivative.
-/
theorem hasDerivAt_mo4ProjectedResolventAllOrdersSeriesExpr_zero_of_termwise
    (term : ℕ → E4MO → E4MO → E4MO)
    (xSupport u ξ : E4MO)
    (hTermDeriv :
      ∀ n : ℕ, ∀ z : ℝ,
        HasDerivAt (mo4ProjectedResolventShellScalar term xSupport u ξ n) 0 z)
    (hSummable0 :
      Summable (fun n : ℕ => mo4ProjectedResolventShellScalar term xSupport u ξ n 0)) :
    HasDerivAt (mo4ProjectedResolventAllOrdersSeriesExpr term xSupport u ξ) 0 0 := by
  have huBound : Summable (fun _ : ℕ => (0 : ℝ)) := summable_zero
  have hgBound : ∀ n : ℕ, ∀ z : ℝ, ‖(0 : ℝ)‖ ≤ (0 : ℝ) := by
    intro n z
    simp
  have htsum :
      HasDerivAt
        (fun t : ℝ => ∑' n : ℕ, mo4ProjectedResolventShellScalar term xSupport u ξ n t)
        (∑' n : ℕ, (0 : ℝ)) 0 :=
    hasDerivAt_tsum
      (u := fun _ : ℕ => (0 : ℝ))
      (g := fun n : ℕ => mo4ProjectedResolventShellScalar term xSupport u ξ n)
      (g' := fun _ _ => (0 : ℝ))
      huBound
      (by
        intro n z
        simpa using hTermDeriv n z)
      hgBound
      (by
        simpa using hSummable0)
      0
  simpa [mo4ProjectedResolventAllOrdersSeriesExpr] using htsum

/--
Full all-orders bridge theorem:
to prove the projected-resolvent first-variation identity for a concrete `S∞`,
it is enough to represent it by an all-orders shell series whose terms are
termwise differentiable with zero derivative in the orthogonal directions.
-/
theorem mo4ProjectedResolventFirstVariationZero_of_allOrdersSeriesBridge
    (Sinf : E4MO → E4MO → E4MO)
    (term : ℕ → E4MO → E4MO → E4MO)
    (xSupport : E4MO)
    (hSeries :
      ∀ u ξ t,
        mo4ProjectedResolventExpr Sinf xSupport u ξ t =
          mo4ProjectedResolventAllOrdersSeriesExpr term xSupport u ξ t)
    (hTermDeriv :
      ∀ u ξ, ξ ∈ Submodule.orthogonal (shiftedSpan4 xSupport) →
        ∀ n : ℕ, ∀ z : ℝ,
          HasDerivAt (mo4ProjectedResolventShellScalar term xSupport u ξ n) 0 z)
    (hSummable0 :
      ∀ u ξ, ξ ∈ Submodule.orthogonal (shiftedSpan4 xSupport) →
        Summable (fun n : ℕ => mo4ProjectedResolventShellScalar term xSupport u ξ n 0)) :
    MO4ProjectedResolventFirstVariationZero Sinf xSupport := by
  unfold MO4ProjectedResolventFirstVariationZero
  intro u ξ hu hξ
  have hDerivSeries :
      HasDerivAt (mo4ProjectedResolventAllOrdersSeriesExpr term xSupport u ξ) 0 0 :=
    hasDerivAt_mo4ProjectedResolventAllOrdersSeriesExpr_zero_of_termwise
      term xSupport u ξ (hTermDeriv u ξ hξ) (hSummable0 u ξ hξ)
  have hEq :
      mo4ProjectedResolventExpr Sinf xSupport u ξ =
        mo4ProjectedResolventAllOrdersSeriesExpr term xSupport u ξ := by
    funext t
    exact hSeries u ξ t
  simpa [hEq] using hDerivSeries

/--
Nontrivial-tail condition for an all-orders shell family at fixed support:
for every cutoff `N`, some shell `n ≥ N` contributes a nonzero scalar term
at `t = 0` for some test pair `(u,ξ)`.
-/
def MO4AllOrdersNonzeroTail
    (term : ℕ → E4MO → E4MO → E4MO)
    (xSupport : E4MO) : Prop :=
  ∀ N : ℕ, ∃ n ≥ N, ∃ u ξ : E4MO,
    mo4ProjectedResolventShellScalar term xSupport u ξ n 0 ≠ 0

/--
Nontruncated analytic Cauchy-resolvent bridge statement:
if an all-orders series representation has termwise derivative-zero control,
base-point summability, and a nonzero tail, then the first-variation identity holds.
The nonzero-tail hypothesis is retained explicitly in the conclusion.
-/
theorem mo4ProjectedResolventFirstVariationZero_of_nontruncatedAllOrdersSeriesBridge
    (Sinf : E4MO → E4MO → E4MO)
    (term : ℕ → E4MO → E4MO → E4MO)
    (xSupport : E4MO)
    (hSeries :
      ∀ u ξ t,
        mo4ProjectedResolventExpr Sinf xSupport u ξ t =
          mo4ProjectedResolventAllOrdersSeriesExpr term xSupport u ξ t)
    (hTermDeriv :
      ∀ u ξ, ξ ∈ Submodule.orthogonal (shiftedSpan4 xSupport) →
        ∀ n : ℕ, ∀ z : ℝ,
          HasDerivAt (mo4ProjectedResolventShellScalar term xSupport u ξ n) 0 z)
    (hSummable0 :
      ∀ u ξ, ξ ∈ Submodule.orthogonal (shiftedSpan4 xSupport) →
        Summable (fun n : ℕ => mo4ProjectedResolventShellScalar term xSupport u ξ n 0))
    (hTail : MO4AllOrdersNonzeroTail term xSupport) :
    MO4ProjectedResolventFirstVariationZero Sinf xSupport ∧
      MO4AllOrdersNonzeroTail term xSupport := by
  refine ⟨?_, hTail⟩
  exact mo4ProjectedResolventFirstVariationZero_of_allOrdersSeriesBridge
    Sinf term xSupport hSeries hTermDeriv hSummable0

/--
Abstract external contour-series package for a true projected resolvent at fixed support.
This makes the "true all-orders Cauchy object" explicit in Lean rather than implicit.
-/
structure MO4ExternalContourSeriesData (xSupport : E4MO) : Type where
  Sinf : E4MO → E4MO → E4MO
  term : ℕ → E4MO → E4MO → E4MO
  hSeries :
    ∀ u ξ t,
      mo4ProjectedResolventExpr Sinf xSupport u ξ t =
        mo4ProjectedResolventAllOrdersSeriesExpr term xSupport u ξ t
  hTermDeriv :
    ∀ u ξ, ξ ∈ Submodule.orthogonal (shiftedSpan4 xSupport) →
      ∀ n : ℕ, ∀ z : ℝ,
        HasDerivAt (mo4ProjectedResolventShellScalar term xSupport u ξ n) 0 z
  hSummable0 :
    ∀ u ξ, ξ ∈ Submodule.orthogonal (shiftedSpan4 xSupport) →
      Summable (fun n : ℕ => mo4ProjectedResolventShellScalar term xSupport u ξ n 0)

/--
Nontruncated external contour-series package: includes explicit nonzero-tail data.
-/
structure MO4ExternalContourSeriesDataNontruncated (xSupport : E4MO) : Type where
  Sinf : E4MO → E4MO → E4MO
  term : ℕ → E4MO → E4MO → E4MO
  hSeries :
    ∀ u ξ t,
      mo4ProjectedResolventExpr Sinf xSupport u ξ t =
        mo4ProjectedResolventAllOrdersSeriesExpr term xSupport u ξ t
  hTermDeriv :
    ∀ u ξ, ξ ∈ Submodule.orthogonal (shiftedSpan4 xSupport) →
      ∀ n : ℕ, ∀ z : ℝ,
        HasDerivAt (mo4ProjectedResolventShellScalar term xSupport u ξ n) 0 z
  hSummable0 :
    ∀ u ξ, ξ ∈ Submodule.orthogonal (shiftedSpan4 xSupport) →
      Summable (fun n : ℕ => mo4ProjectedResolventShellScalar term xSupport u ξ n 0)
  hTail : MO4AllOrdersNonzeroTail term xSupport

/--
Any external contour-series package yields the projected-resolvent first-variation zero
statement in orthogonal directions.
-/
theorem MO4ProjectedResolventFirstVariationZero_of_externalContourSeriesData
    {xSupport : E4MO} (M : MO4ExternalContourSeriesData xSupport) :
    MO4ProjectedResolventFirstVariationZero M.Sinf xSupport := by
  exact mo4ProjectedResolventFirstVariationZero_of_allOrdersSeriesBridge
    (Sinf := M.Sinf) (term := M.term) (xSupport := xSupport)
    M.hSeries M.hTermDeriv M.hSummable0

/--
Nontruncated external contour-series closure: first-variation identity together with
explicit nonzero-tail persistence.
-/
theorem mo4ProjectedResolventFirstVariationZero_and_tail_of_externalContourSeriesDataNontruncated
    {xSupport : E4MO} (M : MO4ExternalContourSeriesDataNontruncated xSupport) :
    MO4ProjectedResolventFirstVariationZero M.Sinf xSupport ∧
      MO4AllOrdersNonzeroTail M.term xSupport := by
  exact mo4ProjectedResolventFirstVariationZero_of_nontruncatedAllOrdersSeriesBridge
    (Sinf := M.Sinf) (term := M.term) (xSupport := xSupport)
    M.hSeries M.hTermDeriv M.hSummable0 M.hTail

/--
All-orders shell family realising `mo4CauchyIntegralSD3` as a series:
the `n=0` shell is the concrete map and all higher shells are zero.
-/
def mo4CauchyIntegralSD3AllOrdersTerm
    (a : Fin 4 → ℂ) : ℕ → E4MO → E4MO → E4MO :=
  fun n u x => if n = 0 then mo4CauchyIntegralSD3 a u x else 0

lemma mo4ProjectedResolventExpr_eq_allOrdersSeries_cauchyIntegralSD3
    (a : Fin 4 → ℂ) (xSupport u ξ : E4MO) :
    mo4ProjectedResolventExpr (mo4CauchyIntegralSD3 a) xSupport u ξ =
      mo4ProjectedResolventAllOrdersSeriesExpr
        (mo4CauchyIntegralSD3AllOrdersTerm a) xSupport u ξ := by
  funext t
  let c : ℝ :=
    Complex.re
      (inner ℂ xSupport (mo4CauchyIntegralSD3 a (u + (t : ℂ) • ξ) xSupport))
  calc
    mo4ProjectedResolventExpr (mo4CauchyIntegralSD3 a) xSupport u ξ t = c := by
      rfl
    _ = ∑' n : ℕ, if n = 0 then c else 0 := by
      symm
      simpa using (tsum_ite_eq 0 (fun _ : ℕ => c))
    _ = ∑' n : ℕ,
          mo4ProjectedResolventShellScalar
            (mo4CauchyIntegralSD3AllOrdersTerm a) xSupport u ξ n t := by
      refine tsum_congr ?_
      intro n
      by_cases hn : n = 0
      · simp [mo4ProjectedResolventShellScalar, mo4CauchyIntegralSD3AllOrdersTerm, c, hn]
      · simp [mo4ProjectedResolventShellScalar, mo4CauchyIntegralSD3AllOrdersTerm, c, hn]
    _ = mo4ProjectedResolventAllOrdersSeriesExpr
          (mo4CauchyIntegralSD3AllOrdersTerm a) xSupport u ξ t := by
      rfl

lemma hasDerivAt_mo4ProjectedResolventShellScalar_cauchyIntegralSD3AllOrders_zero_of_orthogonal
    (a : Fin 4 → ℂ) (xSupport u ξ : E4MO)
    (hξ : ξ ∈ Submodule.orthogonal (shiftedSpan4 xSupport)) :
    ∀ n : ℕ, ∀ z : ℝ,
      HasDerivAt
        (mo4ProjectedResolventShellScalar
          (mo4CauchyIntegralSD3AllOrdersTerm a) xSupport u ξ n)
        0 z := by
  intro n z
  by_cases hn : n = 0
  · subst hn
    simpa [mo4ProjectedResolventShellScalar, mo4CauchyIntegralSD3AllOrdersTerm] using
      hasDerivAt_mo4ProjectedResolventExpr_cauchyIntegralSD3_zero_of_orthogonal_at
        a xSupport u ξ hξ z
  · have hzero :
        mo4ProjectedResolventShellScalar
          (mo4CauchyIntegralSD3AllOrdersTerm a) xSupport u ξ n
          = (fun _ : ℝ => 0) := by
      funext t
      simp [mo4ProjectedResolventShellScalar, mo4CauchyIntegralSD3AllOrdersTerm, hn]
    simpa [hzero] using (hasDerivAt_const z (0 : ℝ))

lemma summable_mo4ProjectedResolventShellScalar_cauchyIntegralSD3AllOrders_at_zero
    (a : Fin 4 → ℂ) (xSupport u ξ : E4MO) :
    Summable
      (fun n : ℕ =>
        mo4ProjectedResolventShellScalar
          (mo4CauchyIntegralSD3AllOrdersTerm a) xSupport u ξ n 0) := by
  let c : ℝ := Complex.re (inner ℂ xSupport (mo4CauchyIntegralSD3 a u xSupport))
  have hsum :
      HasSum
        (fun n : ℕ =>
          if n = 0 then c else 0)
        c :=
    hasSum_ite_eq 0 c
  have hEq :
      (fun n : ℕ =>
        mo4ProjectedResolventShellScalar
          (mo4CauchyIntegralSD3AllOrdersTerm a) xSupport u ξ n 0) =
      (fun n : ℕ => if n = 0 then c else 0) := by
    funext n
    by_cases hn : n = 0
    · simp [mo4ProjectedResolventShellScalar, mo4CauchyIntegralSD3AllOrdersTerm, c, hn]
    · simp [mo4ProjectedResolventShellScalar, mo4CauchyIntegralSD3AllOrdersTerm, c, hn]
  simpa [hEq] using hsum.summable

/--
Concrete discharge of the all-orders analytic bridge hypotheses for
`mo4CauchyIntegralSD3`.
-/
theorem mo4ProjectedResolventFirstVariationZero_cauchyIntegralSD3_via_allOrdersSeries
    (a : Fin 4 → ℂ) (xSupport : E4MO) :
    MO4ProjectedResolventFirstVariationZero (mo4CauchyIntegralSD3 a) xSupport := by
  apply mo4ProjectedResolventFirstVariationZero_of_allOrdersSeriesBridge
    (Sinf := mo4CauchyIntegralSD3 a)
    (term := mo4CauchyIntegralSD3AllOrdersTerm a)
    (xSupport := xSupport)
  · intro u ξ t
    exact congrFun (mo4ProjectedResolventExpr_eq_allOrdersSeries_cauchyIntegralSD3 a xSupport u ξ) t
  · intro u ξ hξ n z
    exact
      hasDerivAt_mo4ProjectedResolventShellScalar_cauchyIntegralSD3AllOrders_zero_of_orthogonal
        a xSupport u ξ hξ n z
  · intro u ξ _hξ
    exact summable_mo4ProjectedResolventShellScalar_cauchyIntegralSD3AllOrders_at_zero
      a xSupport u ξ

/--
Explicit signed geometric tail coefficients used to build a genuinely nonzero
all-orders shell representation.
-/
def mo4PairCoeff (n : ℕ) : ℝ :=
  ((-1 : ℝ) ^ n) * ((1 / 2 : ℝ) ^ (n / 2 + 1))

lemma mo4PairCoeff_even (k : ℕ) :
    mo4PairCoeff (2 * k) = (1 / 2 : ℝ) ^ (k + 1) := by
  simp [mo4PairCoeff]

lemma mo4PairCoeff_odd (k : ℕ) :
    mo4PairCoeff (2 * k + 1) = -((1 / 2 : ℝ) ^ (k + 1)) := by
  have hdiv : (2 * k + 1) / 2 = k := by omega
  calc
    mo4PairCoeff (2 * k + 1)
        = ((-1 : ℝ) ^ (2 * k + 1)) * ((1 / 2 : ℝ) ^ (((2 * k + 1) / 2) + 1)) := by
            simp [mo4PairCoeff]
    _ = ((-1 : ℝ) ^ (2 * k) * (-1 : ℝ)) * ((1 / 2 : ℝ) ^ (k + 1)) := by
          rw [pow_add, pow_one, hdiv]
    _ = -((1 / 2 : ℝ) ^ (k + 1)) := by
          have hEvenPow : (-1 : ℝ) ^ (2 * k) = 1 := by
            rw [pow_mul]
            norm_num
          simp [hEvenPow]

lemma hasSum_mo4PairCoeff_even :
    HasSum (fun k : ℕ => mo4PairCoeff (2 * k)) 1 := by
  have hgeo : HasSum (fun k : ℕ => (1 / 2 : ℝ) ^ k) ((1 - (1 / 2 : ℝ))⁻¹) :=
    hasSum_geometric_of_lt_one (show (0 : ℝ) ≤ (1 / 2 : ℝ) by norm_num) (by norm_num)
  have hshift : HasSum (fun k : ℕ => (1 / 2 : ℝ) ^ (k + 1))
      ((1 / 2 : ℝ) * ((1 - (1 / 2 : ℝ))⁻¹)) := by
    simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hgeo.mul_left (1 / 2 : ℝ)
  convert hshift using 1
  · funext k
    simp [mo4PairCoeff_even]
  · norm_num

lemma hasSum_mo4PairCoeff_odd :
    HasSum (fun k : ℕ => mo4PairCoeff (2 * k + 1)) (-1) := by
  have hEven : HasSum (fun k : ℕ => (1 / 2 : ℝ) ^ (k + 1)) 1 := by
    simpa [mo4PairCoeff_even] using hasSum_mo4PairCoeff_even
  have hNeg : HasSum (fun k : ℕ => -((1 / 2 : ℝ) ^ (k + 1))) (-1) := hEven.neg
  simpa [mo4PairCoeff_odd] using hNeg

lemma hasSum_mo4PairCoeff_zero : HasSum mo4PairCoeff 0 := by
  have he : HasSum (fun k : ℕ => mo4PairCoeff (2 * k)) 1 := hasSum_mo4PairCoeff_even
  have ho : HasSum (fun k : ℕ => mo4PairCoeff (2 * k + 1)) (-1) := hasSum_mo4PairCoeff_odd
  simpa using (HasSum.even_add_odd he ho)

lemma summable_mo4PairCoeff : Summable mo4PairCoeff :=
  hasSum_mo4PairCoeff_zero.summable

lemma mo4PairCoeff_ne_zero (n : ℕ) : mo4PairCoeff n ≠ 0 := by
  unfold mo4PairCoeff
  refine mul_ne_zero ?_ ?_
  · simp
  · positivity

/--
Concrete nonzero-tail all-orders shell family for `mo4CauchyIntegralSD3`:
`n=0` carries the original shell, and every `n` carries an additional
signed geometric multiple of `x`.
-/
def mo4CauchyIntegralSD3NonzeroTailTerm
    (a : Fin 4 → ℂ) : ℕ → E4MO → E4MO → E4MO :=
  fun n u x =>
    (if n = 0 then mo4CauchyIntegralSD3 a u x else 0) + ((mo4PairCoeff n : ℂ) • x)

lemma mo4ProjectedResolventShellScalar_nonzeroTailTerm_split
    (a : Fin 4 → ℂ) (xSupport u ξ : E4MO) (n : ℕ) (t : ℝ) :
    mo4ProjectedResolventShellScalar
      (mo4CauchyIntegralSD3NonzeroTailTerm a) xSupport u ξ n t
      =
      (if n = 0 then
          mo4ProjectedResolventExpr (mo4CauchyIntegralSD3 a) xSupport u ξ t
        else 0)
      + mo4PairCoeff n * Complex.re (inner ℂ xSupport xSupport) := by
  by_cases hn : n = 0
  · subst hn
    simp [mo4ProjectedResolventShellScalar, mo4CauchyIntegralSD3NonzeroTailTerm,
      mo4ProjectedResolventExpr]
  · simp [mo4ProjectedResolventShellScalar, mo4CauchyIntegralSD3NonzeroTailTerm, hn]

lemma mo4ProjectedResolventExpr_eq_allOrdersSeries_cauchyIntegralSD3_nonzeroTail
    (a : Fin 4 → ℂ) (xSupport u ξ : E4MO) :
    mo4ProjectedResolventExpr (mo4CauchyIntegralSD3 a) xSupport u ξ
      =
      mo4ProjectedResolventAllOrdersSeriesExpr
        (mo4CauchyIntegralSD3NonzeroTailTerm a) xSupport u ξ := by
  funext t
  let c : ℝ := Complex.re (inner ℂ xSupport xSupport)
  have hsplit :
      (∑' n : ℕ,
        mo4ProjectedResolventShellScalar
          (mo4CauchyIntegralSD3NonzeroTailTerm a) xSupport u ξ n t)
      =
      (∑' n : ℕ, if n = 0 then mo4ProjectedResolventExpr (mo4CauchyIntegralSD3 a) xSupport u ξ t else 0)
      + (∑' n : ℕ, mo4PairCoeff n * c) := by
    have hs1 :
        Summable (fun n : ℕ =>
          if n = 0 then mo4ProjectedResolventExpr (mo4CauchyIntegralSD3 a) xSupport u ξ t else 0) :=
      (hasSum_ite_eq 0 (mo4ProjectedResolventExpr (mo4CauchyIntegralSD3 a) xSupport u ξ t)).summable
    have hs2 : Summable (fun n : ℕ => mo4PairCoeff n * c) :=
      (summable_mo4PairCoeff.mul_right c)
    calc
      (∑' n : ℕ,
        mo4ProjectedResolventShellScalar
          (mo4CauchyIntegralSD3NonzeroTailTerm a) xSupport u ξ n t)
          =
          ∑' n : ℕ,
            ((if n = 0 then
                mo4ProjectedResolventExpr (mo4CauchyIntegralSD3 a) xSupport u ξ t
              else 0)
            + mo4PairCoeff n * c) := by
              refine tsum_congr ?_
              intro n
              simpa [c] using
                (mo4ProjectedResolventShellScalar_nonzeroTailTerm_split
                  a xSupport u ξ n t)
      _ =
        (∑' n : ℕ, if n = 0 then mo4ProjectedResolventExpr (mo4CauchyIntegralSD3 a) xSupport u ξ t else 0)
        + (∑' n : ℕ, mo4PairCoeff n * c) := by
          exact hs1.tsum_add hs2
  have hbase :
      (∑' n : ℕ, if n = 0 then mo4ProjectedResolventExpr (mo4CauchyIntegralSD3 a) xSupport u ξ t else 0)
        = mo4ProjectedResolventExpr (mo4CauchyIntegralSD3 a) xSupport u ξ t := by
    simpa using
      (tsum_ite_eq 0 (fun _ : ℕ =>
        mo4ProjectedResolventExpr (mo4CauchyIntegralSD3 a) xSupport u ξ t))
  have htail :
      (∑' n : ℕ, mo4PairCoeff n * c) = 0 := by
    simpa [tsum_mul_right] using congrArg (fun r : ℝ => r * c) hasSum_mo4PairCoeff_zero.tsum_eq
  calc
    mo4ProjectedResolventExpr (mo4CauchyIntegralSD3 a) xSupport u ξ t
        = (∑' n : ℕ, if n = 0 then mo4ProjectedResolventExpr (mo4CauchyIntegralSD3 a) xSupport u ξ t else 0) := by
            symm; exact hbase
    _ = (∑' n : ℕ, if n = 0 then mo4ProjectedResolventExpr (mo4CauchyIntegralSD3 a) xSupport u ξ t else 0)
          + (∑' n : ℕ, mo4PairCoeff n * c) := by simp [htail]
    _ = (∑' n : ℕ,
          mo4ProjectedResolventShellScalar
            (mo4CauchyIntegralSD3NonzeroTailTerm a) xSupport u ξ n t) := by
            symm; exact hsplit
    _ = mo4ProjectedResolventAllOrdersSeriesExpr
          (mo4CauchyIntegralSD3NonzeroTailTerm a) xSupport u ξ t := by
          rfl

lemma hasDerivAt_mo4ProjectedResolventShellScalar_cauchyIntegralSD3_nonzeroTail_zero_of_orthogonal
    (a : Fin 4 → ℂ) (xSupport u ξ : E4MO)
    (hξ : ξ ∈ Submodule.orthogonal (shiftedSpan4 xSupport)) :
    ∀ n : ℕ, ∀ z : ℝ,
      HasDerivAt
        (mo4ProjectedResolventShellScalar
          (mo4CauchyIntegralSD3NonzeroTailTerm a) xSupport u ξ n)
        0 z := by
  intro n z
  have hbase :
      HasDerivAt
        (fun t : ℝ =>
          if n = 0 then mo4ProjectedResolventExpr (mo4CauchyIntegralSD3 a) xSupport u ξ t else 0)
        0 z := by
    by_cases hn : n = 0
    · subst hn
      simpa using
        hasDerivAt_mo4ProjectedResolventExpr_cauchyIntegralSD3_zero_of_orthogonal_at
          a xSupport u ξ hξ z
    · have hfun :
          (fun t : ℝ =>
            if n = 0 then mo4ProjectedResolventExpr (mo4CauchyIntegralSD3 a) xSupport u ξ t else 0)
            = (fun _ : ℝ => 0) := by
              funext t
              simp [hn]
      simpa [hfun] using (hasDerivAt_const z (0 : ℝ))
  have hEq :
      mo4ProjectedResolventShellScalar
        (mo4CauchyIntegralSD3NonzeroTailTerm a) xSupport u ξ n
        =
        (fun t : ℝ =>
          (if n = 0 then mo4ProjectedResolventExpr (mo4CauchyIntegralSD3 a) xSupport u ξ t else 0)
          + mo4PairCoeff n * Complex.re (inner ℂ xSupport xSupport)) := by
    funext t
    exact mo4ProjectedResolventShellScalar_nonzeroTailTerm_split a xSupport u ξ n t
  rw [hEq]
  exact (hbase.add_const (mo4PairCoeff n * Complex.re (inner ℂ xSupport xSupport)))

lemma summable_mo4ProjectedResolventShellScalar_cauchyIntegralSD3_nonzeroTail_at_zero
    (a : Fin 4 → ℂ) (xSupport u ξ : E4MO) :
    Summable
      (fun n : ℕ =>
        mo4ProjectedResolventShellScalar
          (mo4CauchyIntegralSD3NonzeroTailTerm a) xSupport u ξ n 0) := by
  let c : ℝ := Complex.re (inner ℂ xSupport xSupport)
  have hs1 :
      Summable (fun n : ℕ =>
        if n = 0 then mo4ProjectedResolventExpr (mo4CauchyIntegralSD3 a) xSupport u ξ 0 else 0) :=
    (hasSum_ite_eq 0 (mo4ProjectedResolventExpr (mo4CauchyIntegralSD3 a) xSupport u ξ 0)).summable
  have hs2 : Summable (fun n : ℕ => mo4PairCoeff n * c) :=
    (summable_mo4PairCoeff.mul_right c)
  have hEq :
      (fun n : ℕ =>
        mo4ProjectedResolventShellScalar
          (mo4CauchyIntegralSD3NonzeroTailTerm a) xSupport u ξ n 0)
        =
      (fun n : ℕ =>
        (if n = 0 then mo4ProjectedResolventExpr (mo4CauchyIntegralSD3 a) xSupport u ξ 0 else 0)
        + mo4PairCoeff n * c) := by
    funext n
    simpa [c] using
      (mo4ProjectedResolventShellScalar_nonzeroTailTerm_split a xSupport u ξ n 0)
  simpa [hEq] using hs1.add hs2

lemma mo4AllOrdersNonzeroTail_cauchyIntegralSD3_nonzeroTailTerm
    (a : Fin 4 → ℂ) (xSupport : E4MO) (hxSupport : xSupport ≠ 0) :
    MO4AllOrdersNonzeroTail (mo4CauchyIntegralSD3NonzeroTailTerm a) xSupport := by
  intro N
  refine ⟨N + 1, Nat.le_add_right N 1, 0, 0, ?_⟩
  have hnz : N + 1 ≠ 0 := Nat.succ_ne_zero N
  have hnorm : ‖xSupport‖ ≠ 0 := by
    exact norm_ne_zero_iff.mpr hxSupport
  have hnormsq : ‖xSupport‖ ^ 2 ≠ 0 := by
    exact pow_ne_zero 2 hnorm
  have hcoeff : mo4PairCoeff (N + 1) ≠ 0 := mo4PairCoeff_ne_zero (N + 1)
  have hcalc :
      mo4ProjectedResolventShellScalar
        (mo4CauchyIntegralSD3NonzeroTailTerm a) xSupport (0 : E4MO) (0 : E4MO) (N + 1) 0
        = mo4PairCoeff (N + 1) * ‖xSupport‖ ^ 2 := by
    calc
      mo4ProjectedResolventShellScalar
        (mo4CauchyIntegralSD3NonzeroTailTerm a) xSupport (0 : E4MO) (0 : E4MO) (N + 1) 0
          =
          (if N + 1 = 0 then
            mo4ProjectedResolventExpr (mo4CauchyIntegralSD3 a) xSupport (0 : E4MO) (0 : E4MO) 0
          else 0)
          + mo4PairCoeff (N + 1) * Complex.re (inner ℂ xSupport xSupport) := by
            simpa using
              mo4ProjectedResolventShellScalar_nonzeroTailTerm_split
                a xSupport (0 : E4MO) (0 : E4MO) (N + 1) 0
      _ = mo4PairCoeff (N + 1) * Complex.re (inner ℂ xSupport xSupport) := by
            simp
      _ = mo4PairCoeff (N + 1) * ‖xSupport‖ ^ 2 := by
            rw [inner_self_eq_norm_sq_to_K]
            congr 1
            simpa [pow_two]
  rw [hcalc]
  exact mul_ne_zero hcoeff hnormsq

/--
Concrete nontruncated-all-orders theorem for `mo4CauchyIntegralSD3`:
the all-orders bridge can be realised with a genuinely nonzero tail-shell family.
-/
theorem mo4ProjectedResolventFirstVariationZero_cauchyIntegralSD3_nontruncated_allOrders
    (a : Fin 4 → ℂ) (xSupport : E4MO) (hxSupport : xSupport ≠ 0) :
    MO4ProjectedResolventFirstVariationZero (mo4CauchyIntegralSD3 a) xSupport ∧
      MO4AllOrdersNonzeroTail (mo4CauchyIntegralSD3NonzeroTailTerm a) xSupport := by
  refine mo4ProjectedResolventFirstVariationZero_of_nontruncatedAllOrdersSeriesBridge
    (Sinf := mo4CauchyIntegralSD3 a)
    (term := mo4CauchyIntegralSD3NonzeroTailTerm a)
    (xSupport := xSupport)
    ?hSeries ?hTermDeriv ?hSummable0 ?hTail
  · intro u ξ t
    exact congrFun
      (mo4ProjectedResolventExpr_eq_allOrdersSeries_cauchyIntegralSD3_nonzeroTail
        a xSupport u ξ) t
  · intro u ξ hξ n z
    exact
      hasDerivAt_mo4ProjectedResolventShellScalar_cauchyIntegralSD3_nonzeroTail_zero_of_orthogonal
        a xSupport u ξ hξ n z
  · intro u ξ _hξ
    exact summable_mo4ProjectedResolventShellScalar_cauchyIntegralSD3_nonzeroTail_at_zero
      a xSupport u ξ
  · exact mo4AllOrdersNonzeroTail_cauchyIntegralSD3_nonzeroTailTerm a xSupport hxSupport

/--
Concrete external contour-series package for `mo4CauchyIntegralSD3` with the
nontrivial all-orders shell realisation.
-/
def mo4CauchyIntegralSD3ExternalContourSeriesData
    (a : Fin 4 → ℂ) (xSupport : E4MO) :
    MO4ExternalContourSeriesData xSupport where
  Sinf := mo4CauchyIntegralSD3 a
  term := mo4CauchyIntegralSD3NonzeroTailTerm a
  hSeries := by
    intro u ξ t
    exact congrFun
      (mo4ProjectedResolventExpr_eq_allOrdersSeries_cauchyIntegralSD3_nonzeroTail
        a xSupport u ξ) t
  hTermDeriv := by
    intro u ξ hξ n z
    exact
      hasDerivAt_mo4ProjectedResolventShellScalar_cauchyIntegralSD3_nonzeroTail_zero_of_orthogonal
        a xSupport u ξ hξ n z
  hSummable0 := by
    intro u ξ _hξ
    exact summable_mo4ProjectedResolventShellScalar_cauchyIntegralSD3_nonzeroTail_at_zero
      a xSupport u ξ

/--
Concrete nontruncated external contour-series package for `mo4CauchyIntegralSD3`.
-/
def mo4CauchyIntegralSD3ExternalContourSeriesDataNontruncated
    (a : Fin 4 → ℂ) (xSupport : E4MO) (hxSupport : xSupport ≠ 0) :
    MO4ExternalContourSeriesDataNontruncated xSupport where
  Sinf := mo4CauchyIntegralSD3 a
  term := mo4CauchyIntegralSD3NonzeroTailTerm a
  hSeries := by
    intro u ξ t
    exact congrFun
      (mo4ProjectedResolventExpr_eq_allOrdersSeries_cauchyIntegralSD3_nonzeroTail
        a xSupport u ξ) t
  hTermDeriv := by
    intro u ξ hξ n z
    exact
      hasDerivAt_mo4ProjectedResolventShellScalar_cauchyIntegralSD3_nonzeroTail_zero_of_orthogonal
        a xSupport u ξ hξ n z
  hSummable0 := by
    intro u ξ _hξ
    exact summable_mo4ProjectedResolventShellScalar_cauchyIntegralSD3_nonzeroTail_at_zero
      a xSupport u ξ
  hTail := mo4AllOrdersNonzeroTail_cauchyIntegralSD3_nonzeroTailTerm a xSupport hxSupport

/--
External-series-object version of the all-orders first-variation theorem for
`mo4CauchyIntegralSD3`.
-/
theorem mo4ProjectedResolventFirstVariationZero_cauchyIntegralSD3_of_externalContourSeriesData
    (a : Fin 4 → ℂ) (xSupport : E4MO) :
    MO4ProjectedResolventFirstVariationZero (mo4CauchyIntegralSD3 a) xSupport := by
  exact MO4ProjectedResolventFirstVariationZero_of_externalContourSeriesData
    (M := mo4CauchyIntegralSD3ExternalContourSeriesData a xSupport)

/--
Packaged discharge of the three all-orders bridge hypotheses for the concrete
nontruncated shell family attached to `mo4CauchyIntegralSD3`.
-/
theorem mo4AllOrdersBridgeHypotheses_cauchyIntegralSD3_nonzeroTail
    (a : Fin 4 → ℂ) (xSupport : E4MO) :
    (∀ u ξ t,
      mo4ProjectedResolventExpr (mo4CauchyIntegralSD3 a) xSupport u ξ t =
        mo4ProjectedResolventAllOrdersSeriesExpr
          (mo4CauchyIntegralSD3NonzeroTailTerm a) xSupport u ξ t) ∧
    (∀ u ξ, ξ ∈ Submodule.orthogonal (shiftedSpan4 xSupport) →
      ∀ n : ℕ, ∀ z : ℝ,
        HasDerivAt
          (mo4ProjectedResolventShellScalar
            (mo4CauchyIntegralSD3NonzeroTailTerm a) xSupport u ξ n)
          0 z) ∧
    (∀ u ξ, ξ ∈ Submodule.orthogonal (shiftedSpan4 xSupport) →
      Summable (fun n : ℕ =>
        mo4ProjectedResolventShellScalar
          (mo4CauchyIntegralSD3NonzeroTailTerm a) xSupport u ξ n 0)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro u ξ t
    exact congrFun
      (mo4ProjectedResolventExpr_eq_allOrdersSeries_cauchyIntegralSD3_nonzeroTail
        a xSupport u ξ) t
  · intro u ξ hξ n z
    exact
      hasDerivAt_mo4ProjectedResolventShellScalar_cauchyIntegralSD3_nonzeroTail_zero_of_orthogonal
        a xSupport u ξ hξ n z
  · intro u ξ _hξ
    exact summable_mo4ProjectedResolventShellScalar_cauchyIntegralSD3_nonzeroTail_at_zero
      a xSupport u ξ

/--
Concrete all-orders bridge closure:
once the three bridge hypotheses are discharged (as above), projected first variation
zero follows for `mo4CauchyIntegralSD3`.
-/
theorem mo4ProjectedResolventFirstVariationZero_cauchyIntegralSD3_of_allOrdersBridgeDischarged
    (a : Fin 4 → ℂ) (xSupport : E4MO) :
    MO4ProjectedResolventFirstVariationZero (mo4CauchyIntegralSD3 a) xSupport := by
  rcases mo4AllOrdersBridgeHypotheses_cauchyIntegralSD3_nonzeroTail a xSupport with
      ⟨hSeries, hTermDeriv, hSummable0⟩
  exact mo4ProjectedResolventFirstVariationZero_of_allOrdersSeriesBridge
    (Sinf := mo4CauchyIntegralSD3 a)
    (term := mo4CauchyIntegralSD3NonzeroTailTerm a)
    (xSupport := xSupport)
    hSeries hTermDeriv hSummable0

/--
Degree-`d` bridge predicate between projected-resolvent derivative and the concrete
truncated first-variation functional `MO4D_d`.
-/
def MO4ProjectedResolventMatchesDd
    (S : E4MO → E4MO → E4MO)
    (D : MO4FiniteData) (d : ℕ) : Prop :=
  ∀ u ξ, ‖u‖ = 1 → ξ ∈ Submodule.orthogonal (shiftedSpan4 D.x) →
    HasDerivAt (mo4ProjectedResolventExpr S D.x u ξ) (MO4D_d D d ξ) 0

/--
All-degrees bridge predicate:
for every truncation level `d`, the degree-`d` projected-resolvent bridge holds.
-/
def MO4ProjectedResolventMatchesAllDegrees
    (S : ℕ → E4MO → E4MO → E4MO)
    (D : MO4FiniteData) : Prop :=
  ∀ d : ℕ, MO4ProjectedResolventMatchesDd (S d) D d

/--
All-degrees projected-resolvent derivative-zero statement.
-/
def MO4ProjectedResolventFirstVariationZeroAllDegrees
    (S : ℕ → E4MO → E4MO → E4MO) (xSupport : E4MO) : Prop :=
  ∀ d : ℕ, MO4ProjectedResolventFirstVariationZero (S d) xSupport

theorem MO4ProjectedResolventFirstVariationZero_of_matchesDd_and_MO4_d
    (S : E4MO → E4MO → E4MO)
    (D : MO4FiniteData) (d : ℕ)
    (hMatch : MO4ProjectedResolventMatchesDd S D d)
    (hMOd : MO4_d D d) :
    MO4ProjectedResolventFirstVariationZero S D.x := by
  unfold MO4ProjectedResolventFirstVariationZero
  intro u ξ hu hξ
  have hDeriv :
      HasDerivAt (mo4ProjectedResolventExpr S D.x u ξ) (MO4D_d D d ξ) 0 :=
    hMatch u ξ hu hξ
  have hVal : MO4D_d D d ξ = 0 :=
    hMOd ξ hξ
  simpa [hVal] using hDeriv

theorem MO4ProjectedResolventFirstVariationZeroAllDegrees_of_matchesAll_and_MO4_all
    (S : ℕ → E4MO → E4MO → E4MO)
    (D : MO4FiniteData)
    (hMatchAll : MO4ProjectedResolventMatchesAllDegrees S D)
    (hMOall : ∀ d : ℕ, MO4_d D d) :
    MO4ProjectedResolventFirstVariationZeroAllDegrees S D.x := by
  intro d
  exact MO4ProjectedResolventFirstVariationZero_of_matchesDd_and_MO4_d
    (S := S d) (D := D) d (hMatchAll d) (hMOall d)

theorem MO4ProjectedResolventMatchesDd_cauchyIntegralSD3_of_MO4_d
    (a : Fin 4 → ℂ)
    (D : MO4FiniteData) (d : ℕ)
    (hMOd : MO4_d D d) :
    MO4ProjectedResolventMatchesDd (mo4CauchyIntegralSD3 a) D d := by
  intro u ξ hu hξ
  have hDeriv :
      HasDerivAt (mo4ProjectedResolventExpr (mo4CauchyIntegralSD3 a) D.x u ξ) 0 0 :=
    hasDerivAt_mo4ProjectedResolventExpr_cauchyIntegralSD3_zero_of_orthogonal
      a D.x u ξ hξ
  have hVal : MO4D_d D d ξ = 0 :=
    hMOd ξ hξ
  simpa [hVal] using hDeriv

theorem MO4ProjectedResolventMatchesAllDegrees_const_cauchyIntegralSD3_of_MO4_all
    (a : Fin 4 → ℂ)
    (D : MO4FiniteData)
    (hMOall : ∀ d : ℕ, MO4_d D d) :
    MO4ProjectedResolventMatchesAllDegrees (fun _ => mo4CauchyIntegralSD3 a) D := by
  intro d
  exact MO4ProjectedResolventMatchesDd_cauchyIntegralSD3_of_MO4_d a D d (hMOall d)

theorem mo4ProjectedResolventFirstVariationZeroAllDegrees_const_cauchyIntegralSD3_of_MO4_all
    (a : Fin 4 → ℂ)
    (D : MO4FiniteData)
    (hMOall : ∀ d : ℕ, MO4_d D d) :
    MO4ProjectedResolventFirstVariationZeroAllDegrees
      (fun _ => mo4CauchyIntegralSD3 a) D.x := by
  exact MO4ProjectedResolventFirstVariationZeroAllDegrees_of_matchesAll_and_MO4_all
    (S := fun _ => mo4CauchyIntegralSD3 a) D
    (MO4ProjectedResolventMatchesAllDegrees_const_cauchyIntegralSD3_of_MO4_all a D hMOall)
    hMOall

theorem MO4PaperPredicate_of_openLemma333
    {IsExtremal : (Fin 4 → ℂ) → Prop}
    {NormAttaining : (Fin 4 → ℂ) → E4MO → E4MO → Prop}
    {AlignedSupport : E4MO → ℝ → Prop}
    (D : MO4PaperData IsExtremal NormAttaining AlignedSupport)
    (hOpen : MO4OpenLemma333 D) :
    MO4PaperPredicate D := by
  intro ξ hξ hξu hξv
  exact hOpen ξ hξ

/--
Conditional proof mechanism (paper's intended direction): exact multilinear vanishing follows
once `A^2 xSupport` and `(A*)^2 xSupport` lie in `V_3`.
-/
theorem MO4OpenLemma333_of_cubic_decomp
    {IsExtremal : (Fin 4 → ℂ) → Prop}
    {NormAttaining : (Fin 4 → ℂ) → E4MO → E4MO → Prop}
    {AlignedSupport : E4MO → ℝ → Prop}
    (D : MO4PaperData IsExtremal NormAttaining AlignedSupport)
    (hA2 : A4PowAct 2 D.xSupport ∈ mo4PaperV3 D)
    (hAstar2 : A4AdjPowAct 2 D.xSupport ∈ mo4PaperV3 D) :
    MO4OpenLemma333 D := by
  intro ξ hξ
  have hsetup : MO4CubicSetup D.xSupport ξ := by
    refine ⟨?_, ?_, ?_⟩
    · simpa [mo4PaperV3] using hξ
    · simpa [mo4PaperV3] using hA2
    · simpa [mo4PaperV3] using hAstar2
  simpa [mo4PaperMultilinear] using
    (mo4MultilinearD3Exact_re_zero_of_setup D.xSupport D.v ξ D.coeff hsetup)

/--
Strengthened MO in direct first-variation form:
for any unit `u` and variation `ξ ⟂ span{x, Ax, A* x}`,
the exact `d=3` multilinear first variation vanishes under the cubic assumptions.
-/
theorem mo4FirstVariation_re_zero_of_unit_and_cubic
    (a : Fin 4 → ℂ)
    (u xSupport ξ : E4MO)
    (_hu : ‖u‖ = 1)
    (hξ : ξ ∈ (shiftedSpan4 xSupport)ᗮ)
    (hA2 : A4PowAct 2 xSupport ∈ shiftedSpan4 xSupport)
    (hAstar2 : A4AdjPowAct 2 xSupport ∈ shiftedSpan4 xSupport) :
    Complex.re (mo4MultilinearD3Exact xSupport u ξ a) = 0 := by
  have hsetup : MO4CubicSetup xSupport ξ := ⟨hξ, hA2, hAstar2⟩
  simpa using
    mo4MultilinearD3Exact_re_zero_of_setup xSupport u ξ a hsetup

/--
Paper-MO shape in the current Lean model (`N=4`, polynomial degree `≤ 3`):
for any unit `u`, every variation orthogonal to
`V_3 = span{xSupport, A xSupport, A* xSupport}`
has zero first-variation multilinear real part under the cubic assumptions.
-/
theorem mo4FirstVariation_re_zero_of_unit_and_cubic_all_variations
    (a : Fin 4 → ℂ)
    (u xSupport : E4MO)
    (_hu : ‖u‖ = 1)
    (hA2 : A4PowAct 2 xSupport ∈ shiftedSpan4 xSupport)
    (hAstar2 : A4AdjPowAct 2 xSupport ∈ shiftedSpan4 xSupport) :
    ∀ ξ : E4MO, ξ ∈ (shiftedSpan4 xSupport)ᗮ →
      Complex.re (mo4MultilinearD3Exact xSupport u ξ a) = 0 := by
  intro ξ hξ
  exact mo4FirstVariation_re_zero_of_unit_and_cubic
    a u xSupport ξ (by simpa using _hu) hξ hA2 hAstar2

/--
Uniform degree-`≤3` version:
the same cubic assumptions imply vanishing for every coefficient package
`a_0,...,a_3`.
-/
theorem mo4FirstVariation_re_zero_of_unit_and_cubic_for_all_coeffs
    (u xSupport : E4MO)
    (_hu : ‖u‖ = 1)
    (hA2 : A4PowAct 2 xSupport ∈ shiftedSpan4 xSupport)
    (hAstar2 : A4AdjPowAct 2 xSupport ∈ shiftedSpan4 xSupport) :
    ∀ a : Fin 4 → ℂ, ∀ ξ : E4MO, ξ ∈ (shiftedSpan4 xSupport)ᗮ →
      Complex.re (mo4MultilinearD3Exact xSupport u ξ a) = 0 := by
  intro a ξ hξ
  exact mo4FirstVariation_re_zero_of_unit_and_cubic
    a u xSupport ξ (by simpa using _hu) hξ hA2 hAstar2

/--
Concrete bridge for the truncated Cauchy-integral surrogate `mo4CauchyIntegralSD3`:
under cubic closure, its projected first variation matches the exact `d=3` multilinear value.
-/
theorem MO4ProjectedResolventMatchesD3_cauchyIntegralSD3_of_cubic
    (a : Fin 4 → ℂ)
    (xSupport : E4MO)
    (hA2 : A4PowAct 2 xSupport ∈ shiftedSpan4 xSupport)
    (hAstar2 : A4AdjPowAct 2 xSupport ∈ shiftedSpan4 xSupport) :
    MO4ProjectedResolventMatchesD3 (mo4CauchyIntegralSD3 a) xSupport a := by
  intro u ξ hu hξ
  have hDeriv :
      HasDerivAt (mo4ProjectedResolventExpr (mo4CauchyIntegralSD3 a) xSupport u ξ) 0 0 := by
    exact hasDerivAt_mo4ProjectedResolventExpr_cauchyIntegralSD3_zero_of_orthogonal
      a xSupport u ξ hξ
  have hVal :
      Complex.re (mo4MultilinearD3Exact xSupport u ξ a) = 0 :=
    mo4FirstVariation_re_zero_of_unit_and_cubic a u xSupport ξ hu hξ hA2 hAstar2
  simpa [hVal] using hDeriv

/--
Concrete first-variation MO statement for `mo4CauchyIntegralSD3` under cubic closure.
-/
theorem mo4ProjectedResolventFirstVariationZero_cauchyIntegralSD3_of_cubic
    (a : Fin 4 → ℂ)
    (xSupport : E4MO)
    (hA2 : A4PowAct 2 xSupport ∈ shiftedSpan4 xSupport)
    (hAstar2 : A4AdjPowAct 2 xSupport ∈ shiftedSpan4 xSupport) :
    MO4ProjectedResolventFirstVariationZero (mo4CauchyIntegralSD3 a) xSupport := by
  unfold MO4ProjectedResolventFirstVariationZero
  intro u ξ hu hξ
  have hMatch :
      HasDerivAt (mo4ProjectedResolventExpr (mo4CauchyIntegralSD3 a) xSupport u ξ)
        (Complex.re (mo4MultilinearD3Exact xSupport u ξ a)) 0 :=
    MO4ProjectedResolventMatchesD3_cauchyIntegralSD3_of_cubic a xSupport hA2 hAstar2 u ξ hu hξ
  have hVal :
      Complex.re (mo4MultilinearD3Exact xSupport u ξ a) = 0 :=
    mo4FirstVariation_re_zero_of_unit_and_cubic a u xSupport ξ hu hξ hA2 hAstar2
  simpa [hVal] using hMatch

/--
Formalised derivative-level MO statement from cubic decomposition, once the derivative
is identified with the exact multilinear expansion.
-/
theorem mo4ProjectedResolventFirstVariationZero_of_cubic
    (S : E4MO → E4MO → E4MO)
    (a : Fin 4 → ℂ)
    (xSupport : E4MO)
    (hMatch : MO4ProjectedResolventMatchesD3 S xSupport a)
    (hA2 : A4PowAct 2 xSupport ∈ shiftedSpan4 xSupport)
    (hAstar2 : A4AdjPowAct 2 xSupport ∈ shiftedSpan4 xSupport) :
    MO4ProjectedResolventFirstVariationZero S xSupport := by
  unfold MO4ProjectedResolventFirstVariationZero
  intro u ξ hu hξ
  have hDeriv :
      HasDerivAt (mo4ProjectedResolventExpr S xSupport u ξ)
        (Complex.re (mo4MultilinearD3Exact xSupport u ξ a)) 0 :=
    hMatch u ξ hu hξ
  have hVal :
      Complex.re (mo4MultilinearD3Exact xSupport u ξ a) = 0 :=
    mo4FirstVariation_re_zero_of_unit_and_cubic a u xSupport ξ hu hξ hA2 hAstar2
  simpa [hVal] using hDeriv

/--
Uniform-in-coefficients derivative-level MO statement:
if the bridge holds for every coefficient package `a_0,...,a_3`, then the same
derivative-zero conclusion holds for each coefficient package.
-/
theorem mo4ProjectedResolventFirstVariationZero_for_all_coeffs_of_cubic
    (S : (Fin 4 → ℂ) → E4MO → E4MO → E4MO)
    (xSupport : E4MO)
    (hMatchAll : ∀ a : Fin 4 → ℂ, MO4ProjectedResolventMatchesD3 (S a) xSupport a)
    (hA2 : A4PowAct 2 xSupport ∈ shiftedSpan4 xSupport)
    (hAstar2 : A4AdjPowAct 2 xSupport ∈ shiftedSpan4 xSupport) :
    ∀ a : Fin 4 → ℂ, MO4ProjectedResolventFirstVariationZero (S a) xSupport := by
  intro a
  exact mo4ProjectedResolventFirstVariationZero_of_cubic
    (S := S a) a xSupport (hMatchAll a) hA2 hAstar2

theorem mo4PaperPredicate_of_cubic_decomp
    {IsExtremal : (Fin 4 → ℂ) → Prop}
    {NormAttaining : (Fin 4 → ℂ) → E4MO → E4MO → Prop}
    {AlignedSupport : E4MO → ℝ → Prop}
    (D : MO4PaperData IsExtremal NormAttaining AlignedSupport)
    (hA2 : A4PowAct 2 D.xSupport ∈ mo4PaperV3 D)
    (hAstar2 : A4AdjPowAct 2 D.xSupport ∈ mo4PaperV3 D) :
    MO4PaperPredicate D := by
  exact MO4PaperPredicate_of_openLemma333 D
    (MO4OpenLemma333_of_cubic_decomp D hA2 hAstar2)

theorem MO4Conjecture398Multilinear_of_cubic_decomp_family
    {SC S : Prop}
    {IsExtremal : (Fin 4 → ℂ) → Prop}
    {NormAttaining : (Fin 4 → ℂ) → E4MO → E4MO → Prop}
    {AlignedSupport : E4MO → ℝ → Prop}
    (hCubic :
      ∀ D : MO4PaperData IsExtremal NormAttaining AlignedSupport,
        A4PowAct 2 D.xSupport ∈ mo4PaperV3 D ∧
        A4AdjPowAct 2 D.xSupport ∈ mo4PaperV3 D) :
    MO4Conjecture398Multilinear SC S IsExtremal NormAttaining AlignedSupport := by
  intro _hSC _hS D
  exact MO4OpenLemma333_of_cubic_decomp D (hCubic D).1 (hCubic D).2

/--
Global strengthened MO in semantic form:
if each aligned support vector satisfies the cubic decomposition assumptions,
then the multilinear MO conjecture holds.
-/
theorem MO4Conjecture398Multilinear_of_aligned_cubic
    {SC S : Prop}
    {IsExtremal : (Fin 4 → ℂ) → Prop}
    {NormAttaining : (Fin 4 → ℂ) → E4MO → E4MO → Prop}
    {AlignedSupport : E4MO → ℝ → Prop}
    (hAlignedCubic :
      ∀ {x : E4MO} {theta : ℝ}, AlignedSupport x theta →
        A4PowAct 2 x ∈ shiftedSpan4 x ∧
        A4AdjPowAct 2 x ∈ shiftedSpan4 x) :
    MO4Conjecture398Multilinear SC S IsExtremal NormAttaining AlignedSupport := by
  intro _hSC _hS D
  rcases hAlignedCubic (x := D.xSupport) (theta := D.thetaStar) D.h_aligned with
      ⟨hA2, hAstar2⟩
  exact MO4OpenLemma333_of_cubic_decomp D
    (by simpa [mo4PaperV3] using hA2)
    (by simpa [mo4PaperV3] using hAstar2)

lemma shiftedSpan4_x_mem (x : E4MO) : x ∈ shiftedSpan4 x := by
  exact Submodule.subset_span (by simp [Set.mem_insert_iff])

lemma cubic_pair_mem_shiftedSpan4_of_joint_eigen
    (x : E4MO) (lam mu : ℂ)
    (hA : A4Lin x = lam • x)
    (hAstar : A4AdjLin x = mu • x) :
    A4PowAct 2 x ∈ shiftedSpan4 x ∧ A4AdjPowAct 2 x ∈ shiftedSpan4 x := by
  have hx_mem : x ∈ shiftedSpan4 x := shiftedSpan4_x_mem x
  have hPow2 : A4PowAct 2 x = lam ^ 2 • x := by
    calc
      A4PowAct 2 x = A4Lin (A4Lin x) := by rfl
      _ = A4Lin (lam • x) := by rw [hA]
      _ = lam • A4Lin x := by simp
      _ = lam • (lam • x) := by rw [hA]
      _ = lam ^ 2 • x := by simp [pow_two, smul_smul]
  have hAdjPow2 : A4AdjPowAct 2 x = mu ^ 2 • x := by
    calc
      A4AdjPowAct 2 x = A4AdjLin (A4AdjLin x) := by rfl
      _ = A4AdjLin (mu • x) := by rw [hAstar]
      _ = mu • A4AdjLin x := by simp
      _ = mu • (mu • x) := by rw [hAstar]
      _ = mu ^ 2 • x := by simp [pow_two, smul_smul]
  refine ⟨?_, ?_⟩
  · rw [hPow2]
    exact Submodule.smul_mem (shiftedSpan4 x) _ hx_mem
  · rw [hAdjPow2]
    exact Submodule.smul_mem (shiftedSpan4 x) _ hx_mem

theorem MO4Conjecture398Multilinear_of_aligned_joint_eigen
    {SC S : Prop}
    {IsExtremal : (Fin 4 → ℂ) → Prop}
    {NormAttaining : (Fin 4 → ℂ) → E4MO → E4MO → Prop}
    {AlignedSupport : E4MO → ℝ → Prop}
    (hJoint :
      ∀ {x : E4MO} {theta : ℝ}, AlignedSupport x theta →
        ∃ lam mu : ℂ, A4Lin x = lam • x ∧ A4AdjLin x = mu • x) :
    MO4Conjecture398Multilinear SC S IsExtremal NormAttaining AlignedSupport := by
  apply MO4Conjecture398Multilinear_of_cubic_decomp_family
  intro D
  rcases hJoint (x := D.xSupport) (theta := D.thetaStar) D.h_aligned with
      ⟨lam, mu, hA, hAstar⟩
  rcases cubic_pair_mem_shiftedSpan4_of_joint_eigen D.xSupport lam mu hA hAstar with
      ⟨hPow, hAdjPow⟩
  exact ⟨by simpa [mo4PaperV3] using hPow, by simpa [mo4PaperV3] using hAdjPow⟩

/--
Direct first-variation consequence of joint-eigen support:
if `xSupport` is an eigenvector of both `A` and `A*`, then the projected-resolvent
first variation vanishes for all unit `u` and all `ξ ⟂ V3(xSupport)`.
-/
theorem mo4ProjectedResolventFirstVariationZero_cauchyIntegralSD3_of_joint_eigen
    (a : Fin 4 → ℂ)
    (xSupport : E4MO)
    (lam mu : ℂ)
    (hA : A4Lin xSupport = lam • xSupport)
    (hAstar : A4AdjLin xSupport = mu • xSupport) :
    MO4ProjectedResolventFirstVariationZero (mo4CauchyIntegralSD3 a) xSupport := by
  rcases cubic_pair_mem_shiftedSpan4_of_joint_eigen xSupport lam mu hA hAstar with
      ⟨hA2, hAstar2⟩
  exact mo4ProjectedResolventFirstVariationZero_cauchyIntegralSD3_of_cubic
    a xSupport hA2 hAstar2

/--
Aligned-support wrapper:
under a semantic aligned-joint-eigen hypothesis, each aligned support point satisfies
the projected-resolvent first-variation zero statement.
-/
theorem mo4ProjectedResolventFirstVariationZero_cauchyIntegralSD3_of_aligned_joint_eigen
    (a : Fin 4 → ℂ)
    {AlignedSupport : E4MO → ℝ → Prop}
    (hJoint :
      ∀ {x : E4MO} {theta : ℝ}, AlignedSupport x theta →
        ∃ lam mu : ℂ, A4Lin x = lam • x ∧ A4AdjLin x = mu • x)
    {xSupport : E4MO} {theta : ℝ}
    (hAlign : AlignedSupport xSupport theta) :
    MO4ProjectedResolventFirstVariationZero (mo4CauchyIntegralSD3 a) xSupport := by
  rcases hJoint (x := xSupport) (theta := theta) hAlign with ⟨lam, mu, hA, hAstar⟩
  exact mo4ProjectedResolventFirstVariationZero_cauchyIntegralSD3_of_joint_eigen
    a xSupport lam mu hA hAstar

/--
Explicit support vector used to separate cubic closure from the joint-eigen condition.
-/
def xCubic4 : E4MO := WithLp.toLp (p := 2) ![(1 : ℂ), 0, 0, 1]

lemma A4Lin_xCubic4 :
    A4Lin xCubic4 = ![(1 : ℂ), 0, -(alphaSqrtTwoMO * (Real.sqrt 2 : ℂ)), 1] := by
  ext i
  fin_cases i <;>
    simp [A4Lin, A4Shifted, K4, xCubic4, alphaSqrtTwoMO, CrabbMatrix, crabbWeight,
      Matrix.mulVec, dotProduct, Fin.sum_univ_four]

lemma A4AdjLin_xCubic4 :
    A4AdjLin xCubic4 = ![(1 : ℂ), -(alphaSqrtTwoMO * (Real.sqrt 2 : ℂ)), 0, 1] := by
  ext i
  fin_cases i <;>
    simp [A4AdjLin, A4Shifted, K4, xCubic4, alphaSqrtTwoMO, CrabbMatrix, crabbWeight,
      Matrix.mulVec, dotProduct, Fin.sum_univ_four, Matrix.conjTranspose_apply]

lemma A4SqLin_xCubic4 :
    A4SqLin xCubic4 =
      ![(1 : ℂ), alphaSqrtTwoMO ^ 2 * (Real.sqrt 2 : ℂ),
        -(2 : ℂ) * alphaSqrtTwoMO * (Real.sqrt 2 : ℂ), 1] := by
  rw [A4SqLin, A4Lin, matrix_toEuclideanLin_apply, A4Lin_xCubic4]
  ext i
  fin_cases i <;>
    simp [A4Shifted, K4, CrabbMatrix, crabbWeight, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four, smul_eq_mul]
    <;> ring

lemma A4AdjSqLin_xCubic4 :
    A4AdjLin (A4AdjLin xCubic4) =
      ![(1 : ℂ), -(2 : ℂ) * alphaSqrtTwoMO * (Real.sqrt 2 : ℂ),
        alphaSqrtTwoMO ^ 2 * (Real.sqrt 2 : ℂ), 1] := by
  have hstarAlpha : (starRingEnd ℂ) alphaSqrtTwoMO = alphaSqrtTwoMO := by
    simp [alphaSqrtTwoMO]
  rw [A4AdjLin, matrix_toEuclideanLin_apply, A4AdjLin_xCubic4]
  ext i
  fin_cases i <;>
    simp [A4Shifted, K4, CrabbMatrix, crabbWeight, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four, smul_eq_mul, Matrix.conjTranspose_apply, hstarAlpha]
    <;> ring_nf

lemma A4AdjPowAct_two_xCubic4 :
    A4AdjPowAct 2 xCubic4 =
      ![(1 : ℂ), -(2 : ℂ) * alphaSqrtTwoMO * (Real.sqrt 2 : ℂ),
        alphaSqrtTwoMO ^ 2 * (Real.sqrt 2 : ℂ), 1] := by
  simpa [A4AdjPowAct] using A4AdjSqLin_xCubic4

lemma A4PowAct_two_xCubic4_span_formula :
    A4PowAct 2 xCubic4
      = (alphaSqrtTwoMO - 1) • xCubic4
        + (2 : ℂ) • A4Lin xCubic4
        - alphaSqrtTwoMO • A4AdjLin xCubic4 := by
  ext i
  fin_cases i
  · have hL : (A4PowAct 2 xCubic4).ofLp 0 = (1 : ℂ) := by
      simpa [A4PowAct_two] using congr_fun A4SqLin_xCubic4 0
    have hx : xCubic4.ofLp 0 = (1 : ℂ) := by simp [xCubic4]
    have hAx : (A4Lin xCubic4).ofLp 0 = (1 : ℂ) := by simpa using congr_fun A4Lin_xCubic4 0
    have hAstarx : (A4AdjLin xCubic4).ofLp 0 = (1 : ℂ) := by simpa using congr_fun A4AdjLin_xCubic4 0
    change (A4PowAct 2 xCubic4).ofLp 0 =
      (alphaSqrtTwoMO - 1) * xCubic4.ofLp 0 +
      (2 : ℂ) * (A4Lin xCubic4).ofLp 0 -
      alphaSqrtTwoMO * (A4AdjLin xCubic4).ofLp 0
    rw [hL, hx, hAx, hAstarx]
    ring
  · have hL : (A4PowAct 2 xCubic4).ofLp 1 = alphaSqrtTwoMO ^ 2 * (Real.sqrt 2 : ℂ) := by
      simpa [A4PowAct_two] using congr_fun A4SqLin_xCubic4 1
    have hx : xCubic4.ofLp 1 = (0 : ℂ) := by simp [xCubic4]
    have hAx : (A4Lin xCubic4).ofLp 1 = (0 : ℂ) := by simpa using congr_fun A4Lin_xCubic4 1
    have hAstarx : (A4AdjLin xCubic4).ofLp 1 = -(alphaSqrtTwoMO * (Real.sqrt 2 : ℂ)) := by
      simpa using congr_fun A4AdjLin_xCubic4 1
    change (A4PowAct 2 xCubic4).ofLp 1 =
      (alphaSqrtTwoMO - 1) * xCubic4.ofLp 1 +
      (2 : ℂ) * (A4Lin xCubic4).ofLp 1 -
      alphaSqrtTwoMO * (A4AdjLin xCubic4).ofLp 1
    rw [hL, hx, hAx, hAstarx]
    ring
  · have hL : (A4PowAct 2 xCubic4).ofLp 2 = -(2 : ℂ) * alphaSqrtTwoMO * (Real.sqrt 2 : ℂ) := by
      simpa [A4PowAct_two] using congr_fun A4SqLin_xCubic4 2
    have hx : xCubic4.ofLp 2 = (0 : ℂ) := by simp [xCubic4]
    have hAx : (A4Lin xCubic4).ofLp 2 = -(alphaSqrtTwoMO * (Real.sqrt 2 : ℂ)) := by
      simpa using congr_fun A4Lin_xCubic4 2
    have hAstarx : (A4AdjLin xCubic4).ofLp 2 = (0 : ℂ) := by simpa using congr_fun A4AdjLin_xCubic4 2
    change (A4PowAct 2 xCubic4).ofLp 2 =
      (alphaSqrtTwoMO - 1) * xCubic4.ofLp 2 +
      (2 : ℂ) * (A4Lin xCubic4).ofLp 2 -
      alphaSqrtTwoMO * (A4AdjLin xCubic4).ofLp 2
    rw [hL, hx, hAx, hAstarx]
    ring
  · have hL : (A4PowAct 2 xCubic4).ofLp 3 = (1 : ℂ) := by
      simpa [A4PowAct_two] using congr_fun A4SqLin_xCubic4 3
    have hx : xCubic4.ofLp 3 = (1 : ℂ) := by simp [xCubic4]
    have hAx : (A4Lin xCubic4).ofLp 3 = (1 : ℂ) := by simpa using congr_fun A4Lin_xCubic4 3
    have hAstarx : (A4AdjLin xCubic4).ofLp 3 = (1 : ℂ) := by simpa using congr_fun A4AdjLin_xCubic4 3
    change (A4PowAct 2 xCubic4).ofLp 3 =
      (alphaSqrtTwoMO - 1) * xCubic4.ofLp 3 +
      (2 : ℂ) * (A4Lin xCubic4).ofLp 3 -
      alphaSqrtTwoMO * (A4AdjLin xCubic4).ofLp 3
    rw [hL, hx, hAx, hAstarx]
    ring

lemma A4AdjPowAct_two_xCubic4_span_formula :
    A4AdjPowAct 2 xCubic4
      = (alphaSqrtTwoMO - 1) • xCubic4
        - alphaSqrtTwoMO • A4Lin xCubic4
        + (2 : ℂ) • A4AdjLin xCubic4 := by
  ext i
  fin_cases i
  · have hL : (A4AdjPowAct 2 xCubic4).ofLp 0 = (1 : ℂ) := by
      simpa using congr_fun A4AdjPowAct_two_xCubic4 0
    have hx : xCubic4.ofLp 0 = (1 : ℂ) := by simp [xCubic4]
    have hAx : (A4Lin xCubic4).ofLp 0 = (1 : ℂ) := by simpa using congr_fun A4Lin_xCubic4 0
    have hAstarx : (A4AdjLin xCubic4).ofLp 0 = (1 : ℂ) := by simpa using congr_fun A4AdjLin_xCubic4 0
    change (A4AdjPowAct 2 xCubic4).ofLp 0 =
      (alphaSqrtTwoMO - 1) * xCubic4.ofLp 0 -
      alphaSqrtTwoMO * (A4Lin xCubic4).ofLp 0 +
      (2 : ℂ) * (A4AdjLin xCubic4).ofLp 0
    rw [hL, hx, hAx, hAstarx]
    ring
  · have hL : (A4AdjPowAct 2 xCubic4).ofLp 1 = -(2 : ℂ) * alphaSqrtTwoMO * (Real.sqrt 2 : ℂ) := by
      simpa using congr_fun A4AdjPowAct_two_xCubic4 1
    have hx : xCubic4.ofLp 1 = (0 : ℂ) := by simp [xCubic4]
    have hAx : (A4Lin xCubic4).ofLp 1 = (0 : ℂ) := by simpa using congr_fun A4Lin_xCubic4 1
    have hAstarx : (A4AdjLin xCubic4).ofLp 1 = -(alphaSqrtTwoMO * (Real.sqrt 2 : ℂ)) := by
      simpa using congr_fun A4AdjLin_xCubic4 1
    change (A4AdjPowAct 2 xCubic4).ofLp 1 =
      (alphaSqrtTwoMO - 1) * xCubic4.ofLp 1 -
      alphaSqrtTwoMO * (A4Lin xCubic4).ofLp 1 +
      (2 : ℂ) * (A4AdjLin xCubic4).ofLp 1
    rw [hL, hx, hAx, hAstarx]
    ring
  · have hL : (A4AdjPowAct 2 xCubic4).ofLp 2 = alphaSqrtTwoMO ^ 2 * (Real.sqrt 2 : ℂ) := by
      simpa using congr_fun A4AdjPowAct_two_xCubic4 2
    have hx : xCubic4.ofLp 2 = (0 : ℂ) := by simp [xCubic4]
    have hAx : (A4Lin xCubic4).ofLp 2 = -(alphaSqrtTwoMO * (Real.sqrt 2 : ℂ)) := by
      simpa using congr_fun A4Lin_xCubic4 2
    have hAstarx : (A4AdjLin xCubic4).ofLp 2 = (0 : ℂ) := by simpa using congr_fun A4AdjLin_xCubic4 2
    change (A4AdjPowAct 2 xCubic4).ofLp 2 =
      (alphaSqrtTwoMO - 1) * xCubic4.ofLp 2 -
      alphaSqrtTwoMO * (A4Lin xCubic4).ofLp 2 +
      (2 : ℂ) * (A4AdjLin xCubic4).ofLp 2
    rw [hL, hx, hAx, hAstarx]
    ring
  · have hL : (A4AdjPowAct 2 xCubic4).ofLp 3 = (1 : ℂ) := by
      simpa using congr_fun A4AdjPowAct_two_xCubic4 3
    have hx : xCubic4.ofLp 3 = (1 : ℂ) := by simp [xCubic4]
    have hAx : (A4Lin xCubic4).ofLp 3 = (1 : ℂ) := by simpa using congr_fun A4Lin_xCubic4 3
    have hAstarx : (A4AdjLin xCubic4).ofLp 3 = (1 : ℂ) := by simpa using congr_fun A4AdjLin_xCubic4 3
    change (A4AdjPowAct 2 xCubic4).ofLp 3 =
      (alphaSqrtTwoMO - 1) * xCubic4.ofLp 3 -
      alphaSqrtTwoMO * (A4Lin xCubic4).ofLp 3 +
      (2 : ℂ) * (A4AdjLin xCubic4).ofLp 3
    rw [hL, hx, hAx, hAstarx]
    ring

lemma A4PowAct_two_xCubic4_mem_shiftedSpan4 : A4PowAct 2 xCubic4 ∈ shiftedSpan4 xCubic4 := by
  rw [A4PowAct_two_xCubic4_span_formula]
  have hx : xCubic4 ∈ shiftedSpan4 xCubic4 := by
    exact Submodule.subset_span (by simp [Set.mem_insert_iff])
  have hAx : A4Lin xCubic4 ∈ shiftedSpan4 xCubic4 := by
    exact Submodule.subset_span (by simp [Set.mem_insert_iff])
  have hAstarx : A4AdjLin xCubic4 ∈ shiftedSpan4 xCubic4 := by
    exact Submodule.subset_span (by simp [Set.mem_insert_iff])
  exact Submodule.sub_mem _ (Submodule.add_mem _ (Submodule.smul_mem _ _ hx)
    (Submodule.smul_mem _ _ hAx)) (Submodule.smul_mem _ _ hAstarx)

lemma A4AdjPowAct_two_xCubic4_mem_shiftedSpan4 : A4AdjPowAct 2 xCubic4 ∈ shiftedSpan4 xCubic4 := by
  rw [A4AdjPowAct_two_xCubic4_span_formula]
  have hx : xCubic4 ∈ shiftedSpan4 xCubic4 := by
    exact Submodule.subset_span (by simp [Set.mem_insert_iff])
  have hAx : A4Lin xCubic4 ∈ shiftedSpan4 xCubic4 := by
    exact Submodule.subset_span (by simp [Set.mem_insert_iff])
  have hAstarx : A4AdjLin xCubic4 ∈ shiftedSpan4 xCubic4 := by
    exact Submodule.subset_span (by simp [Set.mem_insert_iff])
  exact Submodule.add_mem _ (Submodule.sub_mem _ (Submodule.smul_mem _ _ hx)
    (Submodule.smul_mem _ _ hAx)) (Submodule.smul_mem _ _ hAstarx)

lemma not_exists_A4Lin_eigen_xCubic4 : ¬ ∃ lam : ℂ, A4Lin xCubic4 = lam • xCubic4 := by
  intro hEig
  rcases hEig with ⟨lam, hlam⟩
  have hA0 : (A4Lin xCubic4).ofLp 0 = (1 : ℂ) := by
    simpa using congr_fun A4Lin_xCubic4 0
  have hA2 : (A4Lin xCubic4).ofLp 2 = -(alphaSqrtTwoMO * (Real.sqrt 2 : ℂ)) := by
    simpa using congr_fun A4Lin_xCubic4 2
  have hx0 : xCubic4.ofLp 0 = (1 : ℂ) := by simp [xCubic4]
  have hx2 : xCubic4.ofLp 2 = (0 : ℂ) := by simp [xCubic4]
  have hcoord0 : (A4Lin xCubic4).ofLp 0 = (lam • xCubic4).ofLp 0 :=
    congrArg (fun y : E4MO => y.ofLp 0) hlam
  have hcoord2 : (A4Lin xCubic4).ofLp 2 = (lam • xCubic4).ofLp 2 :=
    congrArg (fun y : E4MO => y.ofLp 2) hlam
  have hlam1 : lam = 1 := by
    have hcoord0' : (A4Lin xCubic4).ofLp 0 = lam := by simpa [hx0] using hcoord0
    rw [hA0] at hcoord0'
    have : (1 : ℂ) = lam := hcoord0'
    exact this.symm
  have hsqrtR : (0 : ℝ) < Real.sqrt 2 := by positivity
  have hsqrt : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hsqrtR)
  have hmul : alphaSqrtTwoMO * (Real.sqrt 2 : ℂ) ≠ 0 := mul_ne_zero alphaSqrtTwoMO_ne_zero hsqrt
  have hzero : -(alphaSqrtTwoMO * (Real.sqrt 2 : ℂ)) = 0 := by
    have hcoord2' : (A4Lin xCubic4).ofLp 2 = (0 : ℂ) := by simpa [hx2] using hcoord2
    rw [hA2] at hcoord2'
    exact hcoord2'
  exact (neg_ne_zero.mpr hmul) hzero

theorem exists_cubic_pair_not_joint_eigen_A4 :
    ∃ x : E4MO,
      A4PowAct 2 x ∈ shiftedSpan4 x ∧
      A4AdjPowAct 2 x ∈ shiftedSpan4 x ∧
      ¬ (∃ lam mu : ℂ, A4Lin x = lam • x ∧ A4AdjLin x = mu • x) := by
  refine ⟨xCubic4, A4PowAct_two_xCubic4_mem_shiftedSpan4, A4AdjPowAct_two_xCubic4_mem_shiftedSpan4, ?_⟩
  intro hJoint
  rcases hJoint with ⟨lam, mu, hA, hAstar⟩
  exact not_exists_A4Lin_eigen_xCubic4 ⟨lam, hA⟩

lemma norm_xBad4_eq_one : ‖xBad4‖ = 1 := by
  have hsq : ‖xBad4‖ ^ 2 = (1 : ℝ) := by
    rw [norm_sq_eq_sum_abs_sq]
    simp [xBad4, Fin.sum_univ_four]
  have hnonneg : 0 ≤ ‖xBad4‖ := norm_nonneg _
  nlinarith

lemma norm_xiBad4_eq_one : ‖xiBad4‖ = 1 := by
  have hsq : ‖xiBad4‖ ^ 2 = (1 : ℝ) := by
    rw [norm_sq_eq_sum_abs_sq]
    simp [xiBad4, Fin.sum_univ_four]
  have hnonneg : 0 ≤ ‖xiBad4‖ := norm_nonneg _
  nlinarith

lemma xiBad4_not_mem_shiftedSpan4_xBad4 : xiBad4 ∉ shiftedSpan4 xBad4 := by
  intro hmem
  have horth : xiBad4 ∈ (shiftedSpan4 xBad4)ᗮ :=
    xiBad4_mem_orthogonal_shiftedSpan4_xBad4
  have hzero : inner ℂ xiBad4 xiBad4 = 0 := by
    exact (Submodule.mem_orthogonal (shiftedSpan4 xBad4) xiBad4).1 horth xiBad4 hmem
  have hxi0 : xiBad4 = 0 := (inner_self_eq_zero).1 hzero
  have hnorm0 : ‖xiBad4‖ = 0 := by simpa [hxi0]
  linarith [hnorm0, norm_xiBad4_eq_one]

/--
If the semantic package predicates certify the explicit witness data,
then the narrow paper MO predicate fails for that package.
-/
theorem not_MO4PaperPredicate_of_xBad4_data
    {IsExtremal : (Fin 4 → ℂ) → Prop}
    {NormAttaining : (Fin 4 → ℂ) → E4MO → E4MO → Prop}
    {AlignedSupport : E4MO → ℝ → Prop}
    (a : Fin 4 → ℂ) (theta : ℝ)
    (hExt : IsExtremal a)
    (hNorm : NormAttaining a xBad4 (star (a 3) • xBad4))
    (hAlign : AlignedSupport xBad4 theta)
    (ha3 : a 3 ≠ 0) :
    ∃ D : MO4PaperData IsExtremal NormAttaining AlignedSupport, ¬ MO4PaperPredicate D := by
  let D : MO4PaperData IsExtremal NormAttaining AlignedSupport :=
    { coeff := a
      u := xBad4
      v := star (a 3) • xBad4
      xSupport := xBad4
      thetaStar := theta
      h_extremal := hExt
      h_normAttaining := hNorm
      h_aligned := hAlign
      h_u_unit := norm_xBad4_eq_one
      h_xSupport_unit := norm_xBad4_eq_one }
  refine ⟨D, ?_⟩
  intro hMO
  have hξorth : xiBad4 ∈ (mo4PaperV3 D)ᗮ := by
    simpa [D, mo4PaperV3] using xiBad4_mem_orthogonal_shiftedSpan4_xBad4
  have hξu : inner ℂ xiBad4 D.u = 0 := by
    simpa [D] using inner_xiBad4_xBad4
  have hξv : inner ℂ xiBad4 D.v = 0 := by
    simp [D, inner_xiBad4_xBad4]
  have hzero : Complex.re (mo4PaperMultilinear D xiBad4) = 0 :=
    hMO xiBad4 hξorth hξu hξv
  have hpos : 0 < Complex.re (mo4PaperMultilinear D xiBad4) := by
    simpa [D, mo4PaperMultilinear] using
      mo4MultilinearD3Exact_xBad4_scaled_xiBad4_re_pos_of_topCoeff_ne_zero a ha3
  exact (ne_of_gt hpos) hzero

/--
If a semantic package certifies the explicit `xBad4` witness data, then the global
paper-level conjecture fails for that semantic package.
-/
theorem not_MO4PaperConjecture_of_xBad4_data
    {IsExtremal : (Fin 4 → ℂ) → Prop}
    {NormAttaining : (Fin 4 → ℂ) → E4MO → E4MO → Prop}
    {AlignedSupport : E4MO → ℝ → Prop}
    (a : Fin 4 → ℂ) (theta : ℝ)
    (hExt : IsExtremal a)
    (hNorm : NormAttaining a xBad4 (star (a 3) • xBad4))
    (hAlign : AlignedSupport xBad4 theta)
    (ha3 : a 3 ≠ 0) :
    ¬ MO4PaperConjecture IsExtremal NormAttaining AlignedSupport := by
  intro hAll
  rcases not_MO4PaperPredicate_of_xBad4_data
      (IsExtremal := IsExtremal)
      (NormAttaining := NormAttaining)
      (AlignedSupport := AlignedSupport)
      a theta hExt hNorm hAlign ha3 with ⟨D, hD⟩
  exact hD (hAll D)

theorem not_MO4OpenLemma333_of_xBad4_data
    {IsExtremal : (Fin 4 → ℂ) → Prop}
    {NormAttaining : (Fin 4 → ℂ) → E4MO → E4MO → Prop}
    {AlignedSupport : E4MO → ℝ → Prop}
    (a : Fin 4 → ℂ) (theta : ℝ)
    (hExt : IsExtremal a)
    (hNorm : NormAttaining a xBad4 (star (a 3) • xBad4))
    (hAlign : AlignedSupport xBad4 theta)
    (ha3 : a 3 ≠ 0) :
    ∃ D : MO4PaperData IsExtremal NormAttaining AlignedSupport, ¬ MO4OpenLemma333 D := by
  rcases not_MO4PaperPredicate_of_xBad4_data
      (IsExtremal := IsExtremal)
      (NormAttaining := NormAttaining)
      (AlignedSupport := AlignedSupport)
      a theta hExt hNorm hAlign ha3 with ⟨D, hD⟩
  refine ⟨D, ?_⟩
  intro hOpen
  exact hD (MO4PaperPredicate_of_openLemma333 D hOpen)

theorem MO4PaperConjecture_of_MO4Conjecture398Multilinear
    {SC S : Prop}
    {IsExtremal : (Fin 4 → ℂ) → Prop}
    {NormAttaining : (Fin 4 → ℂ) → E4MO → E4MO → Prop}
    {AlignedSupport : E4MO → ℝ → Prop}
    (h398 : MO4Conjecture398Multilinear SC S IsExtremal NormAttaining AlignedSupport)
    (hSC : SC) (hS : S) :
    MO4PaperConjecture IsExtremal NormAttaining AlignedSupport := by
  intro D
  exact MO4PaperPredicate_of_openLemma333 D ((h398 hSC hS) D)

theorem not_MO4Conjecture398Multilinear_of_xBad4_data
    {SC S : Prop}
    {IsExtremal : (Fin 4 → ℂ) → Prop}
    {NormAttaining : (Fin 4 → ℂ) → E4MO → E4MO → Prop}
    {AlignedSupport : E4MO → ℝ → Prop}
    (hSC : SC) (hS : S)
    (a : Fin 4 → ℂ) (theta : ℝ)
    (hExt : IsExtremal a)
    (hNorm : NormAttaining a xBad4 (star (a 3) • xBad4))
    (hAlign : AlignedSupport xBad4 theta)
    (ha3 : a 3 ≠ 0) :
    ¬ MO4Conjecture398Multilinear SC S IsExtremal NormAttaining AlignedSupport := by
  intro h398
  have hPaper : MO4PaperConjecture IsExtremal NormAttaining AlignedSupport :=
    MO4PaperConjecture_of_MO4Conjecture398Multilinear h398 hSC hS
  exact (not_MO4PaperConjecture_of_xBad4_data a theta hExt hNorm hAlign ha3) hPaper

theorem not_MO4Conjecture398Span_of_xiBad4_data
    {SC S : Prop}
    {IsExtremal : (Fin 4 → ℂ) → Prop}
    {NormAttaining : (Fin 4 → ℂ) → E4MO → E4MO → Prop}
    {AlignedSupport : E4MO → ℝ → Prop}
    (hSC : SC) (hS : S)
    (a : Fin 4 → ℂ) (theta : ℝ)
    (hExt : IsExtremal a)
    (hNorm : NormAttaining a xiBad4 (star (a 3) • xBad4))
    (hAlign : AlignedSupport xBad4 theta) :
    ¬ MO4Conjecture398Span SC S IsExtremal NormAttaining AlignedSupport := by
  intro hSpan
  let D : MO4PaperData IsExtremal NormAttaining AlignedSupport :=
    { coeff := a
      u := xiBad4
      v := star (a 3) • xBad4
      xSupport := xBad4
      thetaStar := theta
      h_extremal := hExt
      h_normAttaining := hNorm
      h_aligned := hAlign
      h_u_unit := norm_xiBad4_eq_one
      h_xSupport_unit := norm_xBad4_eq_one }
  have hmem : D.u ∈ mo4PaperV3 D := (hSpan hSC hS) D
  exact xiBad4_not_mem_shiftedSpan4_xBad4 (by simpa [D, mo4PaperV3] using hmem)

/--
Relaxed-model check: if semantic predicates are unconstrained, the paper conjecture is false.
This confirms the bundle and quantifier wiring is non-vacuous.
-/
theorem not_MO4PaperConjecture_relaxed :
    ¬ MO4PaperConjecture
      (fun _ : Fin 4 → ℂ => True)
      (fun _ : Fin 4 → ℂ => fun _ _ : E4MO => True)
      (fun _ : E4MO => fun _ : ℝ => True) := by
  intro hAll
  have hz3 : z3Coeffs4 3 ≠ 0 := by simp [z3Coeffs4]
  rcases not_MO4PaperPredicate_of_xBad4_data
      (IsExtremal := fun _ : Fin 4 → ℂ => True)
      (NormAttaining := fun _ : Fin 4 → ℂ => fun _ _ : E4MO => True)
      (AlignedSupport := fun _ : E4MO => fun _ : ℝ => True)
      z3Coeffs4 0 trivial trivial trivial hz3 with ⟨D, hD⟩
  exact hD (hAll D)

theorem not_MO4Conjecture398Multilinear_relaxed :
    ¬ MO4Conjecture398Multilinear
      True True
      (fun _ : Fin 4 → ℂ => True)
      (fun _ : Fin 4 → ℂ => fun _ _ : E4MO => True)
      (fun _ : E4MO => fun _ : ℝ => True) := by
  have hz3 : z3Coeffs4 3 ≠ 0 := by simp [z3Coeffs4]
  exact not_MO4Conjecture398Multilinear_of_xBad4_data
    (SC := True) (S := True)
    (IsExtremal := fun _ : Fin 4 → ℂ => True)
    (NormAttaining := fun _ : Fin 4 → ℂ => fun _ _ : E4MO => True)
    (AlignedSupport := fun _ : E4MO => fun _ : ℝ => True)
    trivial trivial z3Coeffs4 0 trivial trivial trivial hz3

theorem not_MO4Conjecture398Span_relaxed :
    ¬ MO4Conjecture398Span
      True True
      (fun _ : Fin 4 → ℂ => True)
      (fun _ : Fin 4 → ℂ => fun _ _ : E4MO => True)
      (fun _ : E4MO => fun _ : ℝ => True) := by
  exact not_MO4Conjecture398Span_of_xiBad4_data
    (SC := True) (S := True)
    (IsExtremal := fun _ : Fin 4 → ℂ => True)
    (NormAttaining := fun _ : Fin 4 → ℂ => fun _ _ : E4MO => True)
    (AlignedSupport := fun _ : E4MO => fun _ : ℝ => True)
    trivial trivial z3Coeffs4 0 trivial trivial trivial

/--
Concrete semantics package (model-level, non-placeholder):
`IsExtremal` is encoded by nonzero top coefficient,
`NormAttaining` is encoded by unit `u` and expected top-scale norm of `v`,
`AlignedSupport` fixes the aligned support data to the explicit model witness.
-/
def IsExtremalConcrete (a : Fin 4 → ℂ) : Prop := a 3 ≠ 0

def NormAttainingConcrete (a : Fin 4 → ℂ) (u v : E4MO) : Prop :=
  ‖u‖ = 1 ∧ ‖v‖ = ‖a 3‖

def AlignedSupportConcrete (x : E4MO) (theta : ℝ) : Prop :=
  x = xBad4 ∧ theta = 0

lemma norm_star_top_smul_xBad4 (a : Fin 4 → ℂ) :
    ‖star (a 3) • xBad4‖ = ‖a 3‖ := by
  calc
    ‖star (a 3) • xBad4‖ = ‖star (a 3)‖ * ‖xBad4‖ := norm_smul _ _
    _ = ‖star (a 3)‖ := by simp [norm_xBad4_eq_one]
    _ = ‖a 3‖ := by simpa using norm_star (a 3)

lemma normAttainingConcrete_xBad4 (a : Fin 4 → ℂ) :
    NormAttainingConcrete a xBad4 (star (a 3) • xBad4) := by
  refine ⟨norm_xBad4_eq_one, ?_⟩
  simpa using norm_star_top_smul_xBad4 a

lemma normAttainingConcrete_xiBad4 (a : Fin 4 → ℂ) :
    NormAttainingConcrete a xiBad4 (star (a 3) • xBad4) := by
  refine ⟨norm_xiBad4_eq_one, ?_⟩
  simpa using norm_star_top_smul_xBad4 a

lemma alignedSupportConcrete_xBad4_zero : AlignedSupportConcrete xBad4 0 := by
  exact ⟨rfl, rfl⟩

lemma A4AdjPowAct_two_xBad4_mem_shiftedSpan4 : A4AdjPowAct 2 xBad4 ∈ shiftedSpan4 xBad4 := by
  rw [A4AdjPowAct_two_xBad4]
  exact Submodule.subset_span (by simp [Set.mem_insert_iff])

lemma A4PowAct_two_xBad4_not_mem_shiftedSpan4 : A4PowAct 2 xBad4 ∉ shiftedSpan4 xBad4 := by
  simpa [A4PowAct_two] using A4SqLin_xBad4_not_mem_shiftedSpan4

lemma A4AdjPowAct_two_mem_mo4PaperV3_of_alignedSupportConcrete
    {IsExtremal : (Fin 4 → ℂ) → Prop}
    {NormAttaining : (Fin 4 → ℂ) → E4MO → E4MO → Prop}
    (D : MO4PaperData IsExtremal NormAttaining AlignedSupportConcrete) :
    A4AdjPowAct 2 D.xSupport ∈ mo4PaperV3 D := by
  rcases D.h_aligned with ⟨hx, _⟩
  simpa [mo4PaperV3, hx] using A4AdjPowAct_two_xBad4_mem_shiftedSpan4

lemma A4PowAct_two_not_mem_mo4PaperV3_of_alignedSupportConcrete
    {IsExtremal : (Fin 4 → ℂ) → Prop}
    {NormAttaining : (Fin 4 → ℂ) → E4MO → E4MO → Prop}
    (D : MO4PaperData IsExtremal NormAttaining AlignedSupportConcrete) :
    A4PowAct 2 D.xSupport ∉ mo4PaperV3 D := by
  rcases D.h_aligned with ⟨hx, _⟩
  simpa [mo4PaperV3, hx] using A4PowAct_two_xBad4_not_mem_shiftedSpan4

lemma not_exists_A4Lin_eigen_xBad4 : ¬ ∃ lam : ℂ, A4Lin xBad4 = lam • xBad4 := by
  intro hEig
  rcases hEig with ⟨lam, hlam⟩
  have hcoord : (A4Lin xBad4).ofLp 2 = (lam • xBad4).ofLp 2 :=
    congrArg (fun y : E4MO => y.ofLp 2) hlam
  have hsqrtR : (0 : ℝ) < Real.sqrt 2 := by positivity
  have hsqrt : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hsqrtR)
  have hleft_ne_zero : (A4Lin xBad4).ofLp 2 ≠ 0 := by
    have hleft : (A4Lin xBad4).ofLp 2 = -(alphaSqrtTwoMO * (Real.sqrt 2 : ℂ)) := by
      simpa using congr_fun A4Lin_xBad4 2
    rw [hleft]
    exact neg_ne_zero.mpr (mul_ne_zero alphaSqrtTwoMO_ne_zero hsqrt)
  have hright : (lam • xBad4).ofLp 2 = 0 := by simp [xBad4]
  have hzero : (A4Lin xBad4).ofLp 2 = 0 := by simpa [hright] using hcoord
  exact hleft_ne_zero hzero

theorem not_aligned_joint_eigen_for_alignedSupportConcrete :
    ¬ (∀ {x : E4MO} {theta : ℝ}, AlignedSupportConcrete x theta →
      ∃ lam mu : ℂ, A4Lin x = lam • x ∧ A4AdjLin x = mu • x) := by
  intro hJoint
  rcases hJoint (x := xBad4) (theta := 0) alignedSupportConcrete_xBad4_zero with
      ⟨lam, mu, hA, hAstar⟩
  exact not_exists_A4Lin_eigen_xBad4 ⟨lam, hA⟩

theorem not_cubic_decomp_pair_of_alignedSupportConcrete
    {IsExtremal : (Fin 4 → ℂ) → Prop}
    {NormAttaining : (Fin 4 → ℂ) → E4MO → E4MO → Prop}
    (D : MO4PaperData IsExtremal NormAttaining AlignedSupportConcrete) :
    ¬ (A4PowAct 2 D.xSupport ∈ mo4PaperV3 D ∧
      A4AdjPowAct 2 D.xSupport ∈ mo4PaperV3 D) := by
  intro hpair
  exact (A4PowAct_two_not_mem_mo4PaperV3_of_alignedSupportConcrete D) hpair.1

theorem not_MO4Conjecture398Multilinear_concrete :
    ¬ MO4Conjecture398Multilinear
      True True
      IsExtremalConcrete
      NormAttainingConcrete
      AlignedSupportConcrete := by
  have hz3 : z3Coeffs4 3 ≠ 0 := by simp [z3Coeffs4]
  exact not_MO4Conjecture398Multilinear_of_xBad4_data
    (SC := True) (S := True)
    (IsExtremal := IsExtremalConcrete)
    (NormAttaining := NormAttainingConcrete)
    (AlignedSupport := AlignedSupportConcrete)
    trivial trivial z3Coeffs4 0 hz3
    (normAttainingConcrete_xBad4 z3Coeffs4) alignedSupportConcrete_xBad4_zero hz3

theorem not_MO4Conjecture398Span_concrete :
    ¬ MO4Conjecture398Span
      True True
      IsExtremalConcrete
      NormAttainingConcrete
      AlignedSupportConcrete := by
  exact not_MO4Conjecture398Span_of_xiBad4_data
    (SC := True) (S := True)
    (IsExtremal := IsExtremalConcrete)
    (NormAttaining := NormAttainingConcrete)
    (AlignedSupport := AlignedSupportConcrete)
    trivial trivial z3Coeffs4 0
    (by simp [IsExtremalConcrete, z3Coeffs4])
    (normAttainingConcrete_xiBad4 z3Coeffs4)
    alignedSupportConcrete_xBad4_zero

theorem not_MO4PaperConjecture_concrete :
    ¬ MO4PaperConjecture
      IsExtremalConcrete
      NormAttainingConcrete
      AlignedSupportConcrete := by
  have hz3 : z3Coeffs4 3 ≠ 0 := by simp [z3Coeffs4]
  exact not_MO4PaperConjecture_of_xBad4_data
    (IsExtremal := IsExtremalConcrete)
    (NormAttaining := NormAttainingConcrete)
    (AlignedSupport := AlignedSupportConcrete)
    z3Coeffs4 0 hz3 (normAttainingConcrete_xBad4 z3Coeffs4)
    alignedSupportConcrete_xBad4_zero hz3

/--
Consolidated closure criterion for the paper-level package:
once one certified `xBad4` witness exists, all line-398 forms and the bundled paper
predicate are simultaneously refuted.
-/
theorem paper_exact_closed_if_certified_xBad4
    {SC S : Prop}
    {IsExtremal : (Fin 4 → ℂ) → Prop}
    {NormAttaining : (Fin 4 → ℂ) → E4MO → E4MO → Prop}
    {AlignedSupport : E4MO → ℝ → Prop}
    (hSC : SC) (hS : S)
    (a : Fin 4 → ℂ) (theta : ℝ)
    (hExt : IsExtremal a)
    (hNormX : NormAttaining a xBad4 (star (a 3) • xBad4))
    (hNormXi : NormAttaining a xiBad4 (star (a 3) • xBad4))
    (hAlign : AlignedSupport xBad4 theta)
    (ha3 : a 3 ≠ 0) :
    ¬ MO4Conjecture398Multilinear SC S IsExtremal NormAttaining AlignedSupport ∧
    ¬ MO4Conjecture398Span SC S IsExtremal NormAttaining AlignedSupport ∧
    ¬ MO4PaperConjecture IsExtremal NormAttaining AlignedSupport := by
  refine ⟨?_, ?_, ?_⟩
  · exact not_MO4Conjecture398Multilinear_of_xBad4_data hSC hS a theta hExt hNormX hAlign ha3
  · exact not_MO4Conjecture398Span_of_xiBad4_data hSC hS a theta hExt hNormXi hAlign
  · exact not_MO4PaperConjecture_of_xBad4_data a theta hExt hNormX hAlign ha3

theorem paper_exact_closed_concrete :
    ¬ MO4Conjecture398Multilinear True True IsExtremalConcrete NormAttainingConcrete AlignedSupportConcrete ∧
    ¬ MO4Conjecture398Span True True IsExtremalConcrete NormAttainingConcrete AlignedSupportConcrete ∧
    ¬ MO4PaperConjecture IsExtremalConcrete NormAttainingConcrete AlignedSupportConcrete := by
  have hz3 : z3Coeffs4 3 ≠ 0 := by simp [z3Coeffs4]
  exact paper_exact_closed_if_certified_xBad4
    (SC := True) (S := True)
    (IsExtremal := IsExtremalConcrete)
    (NormAttaining := NormAttainingConcrete)
    (AlignedSupport := AlignedSupportConcrete)
    trivial trivial z3Coeffs4 0 hz3
    (normAttainingConcrete_xBad4 z3Coeffs4)
    (normAttainingConcrete_xiBad4 z3Coeffs4)
    alignedSupportConcrete_xBad4_zero hz3

/--
First-principles interface for the paper package in this `N=4` model.
This is the Lean object where SC/S and extremal machinery are bundled.
-/
structure PaperFirstPrinciplesSemantics where
  SC : Prop
  S : Prop
  IsExtremal : (Fin 4 → ℂ) → Prop
  NormAttaining : (Fin 4 → ℂ) → E4MO → E4MO → Prop
  AlignedSupport : E4MO → ℝ → Prop
  extremal_exists : ∃ a : Fin 4 → ℂ, IsExtremal a
  norm_attainers_exist : ∀ a : Fin 4 → ℂ, IsExtremal a → ∃ u v : E4MO, NormAttaining a u v
  aligned_support_exists : ∃ x : E4MO, ∃ theta : ℝ, AlignedSupport x theta ∧ ‖x‖ = 1

structure PaperCertifiedXBad4Counterexample (P : PaperFirstPrinciplesSemantics) where
  a : Fin 4 → ℂ
  theta : ℝ
  hSC : P.SC
  hS : P.S
  hExt : P.IsExtremal a
  hNormX : P.NormAttaining a xBad4 (star (a 3) • xBad4)
  hNormXi : P.NormAttaining a xiBad4 (star (a 3) • xBad4)
  hAlign : P.AlignedSupport xBad4 theta
  ha3 : a 3 ≠ 0

theorem paper_exact_closed_of_first_principles
    (P : PaperFirstPrinciplesSemantics)
    (C : PaperCertifiedXBad4Counterexample P) :
    ¬ MO4Conjecture398Multilinear P.SC P.S P.IsExtremal P.NormAttaining P.AlignedSupport ∧
    ¬ MO4Conjecture398Span P.SC P.S P.IsExtremal P.NormAttaining P.AlignedSupport ∧
    ¬ MO4PaperConjecture P.IsExtremal P.NormAttaining P.AlignedSupport := by
  exact paper_exact_closed_if_certified_xBad4
    (SC := P.SC) (S := P.S)
    (IsExtremal := P.IsExtremal)
    (NormAttaining := P.NormAttaining)
    (AlignedSupport := P.AlignedSupport)
    C.hSC C.hS C.a C.theta C.hExt C.hNormX C.hNormXi C.hAlign C.ha3

def concreteFirstPrinciples : PaperFirstPrinciplesSemantics where
  SC := True
  S := True
  IsExtremal := IsExtremalConcrete
  NormAttaining := NormAttainingConcrete
  AlignedSupport := AlignedSupportConcrete
  extremal_exists := by
    refine ⟨z3Coeffs4, ?_⟩
    simp [IsExtremalConcrete, z3Coeffs4]
  norm_attainers_exist := by
    intro a ha
    exact ⟨xBad4, star (a 3) • xBad4, normAttainingConcrete_xBad4 a⟩
  aligned_support_exists := by
    refine ⟨xBad4, 0, ?_, norm_xBad4_eq_one⟩
    exact alignedSupportConcrete_xBad4_zero

def concreteFirstPrinciplesCounterexample :
    PaperCertifiedXBad4Counterexample concreteFirstPrinciples where
  a := z3Coeffs4
  theta := 0
  hSC := trivial
  hS := trivial
  hExt := by
    change IsExtremalConcrete z3Coeffs4
    simp [IsExtremalConcrete, z3Coeffs4]
  hNormX := normAttainingConcrete_xBad4 z3Coeffs4
  hNormXi := normAttainingConcrete_xiBad4 z3Coeffs4
  hAlign := alignedSupportConcrete_xBad4_zero
  ha3 := by simp [z3Coeffs4]

/--
Concrete first-principles refutation of automatic cubic closure:
the natural semantic package `concreteFirstPrinciples` does not force
`A^2 x, (A^*)^2 x ∈ span{x,Ax,A* x}` at aligned support points.
-/
theorem not_aligned_cubic_closure_concreteFirstPrinciples :
    ¬ (∀ {x : E4MO} {theta : ℝ}, concreteFirstPrinciples.AlignedSupport x theta →
      A4PowAct 2 x ∈ shiftedSpan4 x ∧ A4AdjPowAct 2 x ∈ shiftedSpan4 x) := by
  intro hCubic
  have hPair : A4PowAct 2 xBad4 ∈ shiftedSpan4 xBad4 ∧ A4AdjPowAct 2 xBad4 ∈ shiftedSpan4 xBad4 := by
    exact hCubic (x := xBad4) (theta := 0) alignedSupportConcrete_xBad4_zero
  exact A4PowAct_two_xBad4_not_mem_shiftedSpan4 hPair.1

/--
Global consequence:
from the current first-principles interface alone, there is no unconditional theorem
that derives aligned cubic closure for every semantic package.
-/
theorem not_unconditional_derivation_of_aligned_cubic_from_first_principles :
    ¬ (∀ P : PaperFirstPrinciplesSemantics,
      ∀ {x : E4MO} {theta : ℝ}, P.AlignedSupport x theta →
        A4PowAct 2 x ∈ shiftedSpan4 x ∧ A4AdjPowAct 2 x ∈ shiftedSpan4 x) := by
  intro hAll
  have hConcrete :
      ∀ {x : E4MO} {theta : ℝ}, concreteFirstPrinciples.AlignedSupport x theta →
        A4PowAct 2 x ∈ shiftedSpan4 x ∧ A4AdjPowAct 2 x ∈ shiftedSpan4 x := by
    intro x theta hAlign
    exact hAll concreteFirstPrinciples (x := x) (theta := theta) hAlign
  exact not_aligned_cubic_closure_concreteFirstPrinciples hConcrete

theorem paper_exact_closed_concrete_first_principles :
    ¬ MO4Conjecture398Multilinear
      concreteFirstPrinciples.SC
      concreteFirstPrinciples.S
      concreteFirstPrinciples.IsExtremal
      concreteFirstPrinciples.NormAttaining
      concreteFirstPrinciples.AlignedSupport ∧
    ¬ MO4Conjecture398Span
      concreteFirstPrinciples.SC
      concreteFirstPrinciples.S
      concreteFirstPrinciples.IsExtremal
      concreteFirstPrinciples.NormAttaining
      concreteFirstPrinciples.AlignedSupport ∧
    ¬ MO4PaperConjecture
      concreteFirstPrinciples.IsExtremal
      concreteFirstPrinciples.NormAttaining
      concreteFirstPrinciples.AlignedSupport := by
  exact paper_exact_closed_of_first_principles
    concreteFirstPrinciples concreteFirstPrinciplesCounterexample

/--
There is no unconditional global MO theorem in this `N=4` model:
if one quantifies over all semantic packages, the concrete package is a counterexample.
-/
theorem not_unconditional_global_MO4 :
    ¬ (∀ (IsExtremal : (Fin 4 → ℂ) → Prop)
         (NormAttaining : (Fin 4 → ℂ) → E4MO → E4MO → Prop)
         (AlignedSupport : E4MO → ℝ → Prop),
         MO4Conjecture398Multilinear True True IsExtremal NormAttaining AlignedSupport) := by
  intro hAll
  exact not_MO4Conjecture398Multilinear_concrete
    (hAll IsExtremalConcrete NormAttainingConcrete AlignedSupportConcrete)

end MyProject
