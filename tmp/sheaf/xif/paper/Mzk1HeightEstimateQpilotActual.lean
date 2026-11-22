/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface
import tmp.sheaf.xif.paper.Mzk1ABCEstimatesArithmeticQpilotActual
import Mathlib.Tactic

/-! # Mzk1HeightEstimateQpilotActual — HeightEstimate substantive advance (A611)

Given the bridge comparison data, the Gap-1 height comparison is chained with the
Gap-2 log-volume estimate and absorbed: for `0 ≤ ε ≤ 1` there is `D` such that
`logHeight ≤ (1+3ε)·weight + (1+ε)·(θ + D)` on all ABC triples.  This is a real
derivation (height estimate), not just a re-export; the named fields of the
comparison data remain the unproved paper links. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.Mzk1HeightEstimateQpilotActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1ABCEstimatesArithmeticQpilotActual
open MeasureTheory
open scoped ENNReal

universe u

/-- **Height estimate**: from the bridge comparison data, for `0 ≤ ε ≤ 1` the
height is bounded by `(1+3ε)·weight + (1+ε)·(θ + D)` with a constant `D`.
-/
theorem height_estimate {X : Type u} {W : IQHullLogVolumeInterface X} {epsilon : Real}
    (C : Cor312EpsilonArithmeticComparison W epsilon)
    (h0 : 0 ≤ epsilon) (h1 : epsilon ≤ 1) :
    ∃ D : Real, ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + 3 * epsilon) * arithmeticWeight (abcRationalPoint a c) +
          (1 + epsilon) * ((W.logVolume W.hull).toReal + D) := by
  obtain ⟨D, hD⟩ := C.regionVolume_le_normalizedWeight
  refine ⟨D, fun a b c habc => ?_⟩
  have hge1 := C.height_le_normalizedRegionVolume a b c habc
  have hge2 := hD a b c habc
  have hw : (0 : Real) ≤ arithmeticWeight (abcRationalPoint a c) :=
    arithmeticWeight_nonneg _
  exact height_le_absorbed h0 h1 hw (height_le_of_twoEstimates h0 hge1 hge2)

/-- Height estimate in `∃ A` form (absorbing the θ+D part into a single constant
dependent on `ε` and the data). -/
theorem height_estimate_exists {X : Type u} {W : IQHullLogVolumeInterface X}
    {epsilon : Real} (C : Cor312EpsilonArithmeticComparison W epsilon)
    (h0 : 0 ≤ epsilon) (h1 : epsilon ≤ 1) :
    ∃ A : Real, ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + 3 * epsilon) * arithmeticWeight (abcRationalPoint a c) + A := by
  obtain ⟨D, hD⟩ := height_estimate C h0 h1
  refine ⟨(1 + epsilon) * ((W.logVolume W.hull).toReal + D), fun a b c habc => ?_⟩
  exact hD a b c habc

#check height_estimate
#check height_estimate_exists

end LeanFormal.IUT.XiFPaper.Mzk1HeightEstimateQpilotActual
end
