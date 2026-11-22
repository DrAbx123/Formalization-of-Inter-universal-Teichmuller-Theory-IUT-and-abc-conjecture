import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic

/-! # Mzk1AnnulusDiffAbstractActual — annulus measure and strict increase (abstract)

A563 chain-independent module (no new mathematics): the abstract measure-theory content
of the annulus strict-measure chain: for finite measure `μ`, measurable `A` and
`B \ A`, a positive measure annulus implies `μ A < μ B`.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1AnnulusDiffAbstractActual

open MeasureTheory
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α]

/-- If `A` is measurable, `B \ A` has positive finite-related measure and `μ A`, `μ B`
are finite, then `μ A < μ B` (measure of the disjoint union). -/
theorem measure_lt_of_annulus_pos {μ : Measure α}
    {A B : Set α} (hA : MeasurableSet A) (hAB : A ⊆ B)
    (hB : μ B < ⊤) (hann : 0 < μ (B \ A)) : μ A < μ B := by
  have hdisj : Disjoint A (B \ A) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact hx'.2 hx
  have hadd : μ (A ∪ (B \ A)) = μ A + μ (B \ A) := measure_union hdisj hA
  have hunion : A ∪ (B \ A) = B := by
    ext x
    constructor
    · rintro (hx | ⟨hx, _⟩)
      · exact hAB hx
      · exact hx
    · intro hx
      by_cases h : x ∈ A
      · exact Or.inl h
      · exact Or.inr ⟨hx, h⟩
  have hfinA : μ A ≠ ⊤ := ne_top_of_le_ne_top hB.ne (measure_mono hAB)
  calc μ A < μ A + μ (B \ A) := ENNReal.lt_add_right hfinA hann.ne'
    _ = μ (A ∪ (B \ A)) := hadd.symm
    _ = μ B := by rw [hunion]

#check measure_lt_of_annulus_pos

end LeanFormal.IUT.XiFPaper.Mzk1AnnulusDiffAbstractActual
end
