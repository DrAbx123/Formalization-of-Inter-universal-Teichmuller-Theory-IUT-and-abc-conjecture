/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1HeightEstimateQpilotActual
import tmp.sheaf.xif.paper.Mzk1VolumeEstimateQpilotActual
import Mathlib.Tactic

/-! # Mzk1ABCTwoEstimatesModelQpilotActual — model-level reduction (A612)

Real model advance: a per-ε family of bridge comparison data yields the global
height-weight bound shape of IUT IV Theorem A (conditional on the two named
comparison fields carried by the data).  The `ε`-reparametrization
`δ = min (ε/4) 1` keeps `(1+3δ) ≤ (1+ε)`. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesModelQpilotActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1HeightEstimateQpilotActual
open LeanFormal.IUT.XiFPaper.Mzk1VolumeEstimateQpilotActual
open MeasureTheory
open scoped ENNReal

universe u

/-- The global additive height-weight bound shape (IUT IV Theorem A). -/
def HeightWeightBoundShape : Prop :=
  ∀ epsilon : Real, 0 < epsilon → ∃ A : Real,
    ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) + A

/-- From a per-`ε` family of comparison data, the global height-weight bound shape
follows (using `height_estimate_exists` and the `δ = min (ε/4) 1` reparametrization). -/
theorem heightWeightBoundShape_of_family {X : Type u} {W : IQHullLogVolumeInterface X}
    (C : ∀ epsilon : Real, 0 < epsilon → Cor312EpsilonArithmeticComparison W epsilon) :
    HeightWeightBoundShape := by
  intro epsilon hepsilon
  let delta : Real := min (epsilon / 4) 1
  have hdelta_pos : 0 < delta := by
    unfold delta
    have : 0 < epsilon / 4 := by linarith
    exact lt_min this (by norm_num)
  have hdelta_le : delta ≤ 1 := by
    unfold delta
    exact min_le_right _ _
  have hdelta_eps : 3 * delta ≤ epsilon := by
    unfold delta
    have hle : delta ≤ epsilon / 4 := by
      unfold delta
      exact min_le_left _ _
    linarith
  obtain ⟨A0, hA0⟩ := height_estimate_exists (C delta hdelta_pos) (le_of_lt hdelta_pos) hdelta_le
  refine ⟨A0, fun a b c habc => ?_⟩
  have hh := hA0 a b c habc
  have hw : (0 : Real) ≤ arithmeticWeight (abcRationalPoint a c) :=
    arithmeticWeight_nonneg _
  have hmul : (1 + 3 * delta) * arithmeticWeight (abcRationalPoint a c) ≤
      (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) := by
    nlinarith
  linarith

/-! ### Gate verification -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1HeightEstimateQpilotActual.height_estimate
#print axioms LeanFormal.IUT.XiFPaper.Mzk1HeightEstimateQpilotActual.height_estimate_exists
#print axioms LeanFormal.IUT.XiFPaper.Mzk1VolumeEstimateQpilotActual.volume_estimate_exists
#print axioms heightWeightBoundShape_of_family

#check heightWeightBoundShape_of_family

end LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesModelQpilotActual
end
