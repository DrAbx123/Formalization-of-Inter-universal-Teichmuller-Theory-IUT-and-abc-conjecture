import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi parameterized single-point null measure

Per-coordinate null-singleton measures imply null singletons of the finite product
measure. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXISinglePointNullParameterizedActual

open MeasureTheory

theorem pi_singleton_null {ι : Type*} [Fintype ι]
    {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : ∀ i, Measure (X i)) [∀ i, NullSingletonClass (μ i)]
    (x : ∀ i, X i) :
    Measure.pi μ ({x} : Set (∀ i, X i)) = 0 := by
  have hset : ({x} : Set (∀ i, X i)) = Set.pi Set.univ (fun i => {x i}) := by
    ext y
    simp [Set.mem_pi]
  rw [hset, Measure.pi_pi]
  exact Finset.prod_eq_zero (Finset.mem_univ _) (measure_singleton (x := x) _)

theorem pi_null_singleton_class {ι : Type*} [Fintype ι]
    {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : ∀ i, Measure (X i)) [∀ i, NullSingletonClass (μ i)] :
    NullSingletonClass (Measure.pi μ) where
  measure_singleton x := pi_singleton_null μ x

end LeanFormal.IUT.XiFPaper.Mzk1StepXISinglePointNullParameterizedActual

end
