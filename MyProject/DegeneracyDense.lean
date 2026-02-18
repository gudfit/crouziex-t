import Mathlib

noncomputable section

open MeasureTheory
open MeasureTheory.Measure

namespace MyProject

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

abbrev GoodSet (n : ℕ) (SC S : Mat n → Prop) : Set (Mat n) :=
  {A : Mat n | SC A ∧ S A}

/--
Literal schema corresponding to the paper sentence when `(SC)` and `(S)` are treated as
unspecified predicates on matrices.
-/
def LemDegenStatement (n : ℕ) : Prop :=
  ∀ SC S : Mat n → Prop, Dense (GoodSet n SC S)

instance matrixMeasurableSpace (n : ℕ) : MeasurableSpace (Mat n) := by
  delta Mat Matrix
  infer_instance

instance matrixBorelSpace (n : ℕ) : BorelSpace (Mat n) := by
  delta Mat Matrix
  infer_instance

lemma ae_of_null_compl
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    (μ : Measure α) (P : α → Prop)
    (hP : μ {x | ¬ P x} = 0) :
    ∀ᵐ x ∂ μ, P x := by
  rw [ae_iff]
  exact hP

lemma dense_of_two_null_compl
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    (μ : Measure α) [Measure.IsOpenPosMeasure μ]
    (P Q : α → Prop)
    (hP : μ {x | ¬ P x} = 0)
    (hQ : μ {x | ¬ Q x} = 0) :
    Dense {x | P x ∧ Q x} := by
  have hPae : ∀ᵐ x ∂ μ, P x := ae_of_null_compl (μ := μ) (P := P) hP
  have hQae : ∀ᵐ x ∂ μ, Q x := ae_of_null_compl (μ := μ) (P := Q) hQ
  exact Measure.dense_of_ae (μ := μ) (hPae.and hQae)

theorem lem_degen
    (n : ℕ)
    (μ : Measure (Mat n)) [Measure.IsOpenPosMeasure μ]
    (SC S : Mat n → Prop)
    (hSC : μ {A | ¬ SC A} = 0)
    (hS : μ {A | ¬ S A} = 0) :
    Dense (GoodSet n SC S) := by
  exact dense_of_two_null_compl (μ := μ) (P := SC) (Q := S) hSC hS

theorem lem_degen_n_ge_two
    (n : ℕ) (_hn : 2 ≤ n)
    (μ : Measure (Mat n)) [Measure.IsOpenPosMeasure μ]
    (SC S : Mat n → Prop)
    (hSC : μ {A | ¬ SC A} = 0)
    (hS : μ {A | ¬ S A} = 0) :
    Dense (GoodSet n SC S) := by
  exact lem_degen n μ SC S hSC hS

/--
Disproof of the unconditional strengthening:
without hypotheses on the bad sets, `Dense (GoodSet n SC S)` cannot hold for all predicates.
-/
theorem not_unconditional_degeneracy (n : ℕ) :
    ¬ LemDegenStatement n := by
  intro hAll
  have hFalse : Dense (GoodSet n (fun _ => False) (fun _ => True)) :=
    hAll (fun _ => False) (fun _ => True)
  have hEmptyDense : Dense (∅ : Set (Mat n)) := by
    simpa [GoodSet] using hFalse
  have hEq : (∅ : Set (Mat n)) = Set.univ := by
    simpa [dense_iff_closure_eq] using hEmptyDense
  exact Set.empty_ne_univ hEq

theorem not_dense_of_eq_empty
    (n : ℕ) (SC S : Mat n → Prop)
    (hEmpty : GoodSet n SC S = ∅) :
    ¬ Dense (GoodSet n SC S) := by
  intro hDense
  have hEq : (∅ : Set (Mat n)) = Set.univ := by
    simpa [hEmpty, dense_iff_closure_eq] using hDense
  exact Set.empty_ne_univ hEq

theorem not_dense_of_forall_not
    (n : ℕ) (SC S : Mat n → Prop)
    (hNone : ∀ A : Mat n, ¬ (SC A ∧ S A)) :
    ¬ Dense (GoodSet n SC S) := by
  have hEmpty : GoodSet n SC S = ∅ := by
    ext A
    simp [GoodSet, hNone A]
  exact not_dense_of_eq_empty n SC S hEmpty

theorem not_lem_degenStatement_n1 : ¬ LemDegenStatement 1 :=
  not_unconditional_degeneracy 1

end MyProject
