import tmp.sheaf.xif.paper.Mzk1StepXIGap1MonotonicityActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi corrected-region Gap1 inverse scaling

Inverse scaling law for the Gap1 comparison: dividing the height bound by a
positive factor preserves the comparison. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXICorrectedRegionGap1Actual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1ABCBridgeHeightRegionActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIGap1MonotonicityActual

universe u

theorem gap1_inv_scaling (X : Type u) (W : IQHullLogVolumeInterface X)
    (logShellPoint : Nat → Nat → Nat → X)
    {ε : Real} (D : StepXIGap1Comparison X W logShellPoint ε)
    (a b c : Nat) (habc : IsABCTriple a b c)
    {s : Real} (hs : 0 < s) :
    Height.logHeight₁ (abcRationalPoint a c) / s ≤
      ((1 + ε) * (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal) / s := by
  have h := D.height_le a b c habc
  exact div_le_div_of_nonneg_right h hs.le

theorem gap1_inv_scaling_iff (X : Type u) (W : IQHullLogVolumeInterface X)
    (logShellPoint : Nat → Nat → Nat → X)
    {ε : Real} (D : StepXIGap1Comparison X W logShellPoint ε)
    (a b c : Nat) (habc : IsABCTriple a b c)
    {s : Real} (hs : 0 < s) :
    Height.logHeight₁ (abcRationalPoint a c) ≤
      (1 + ε) * (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal ↔
      Height.logHeight₁ (abcRationalPoint a c) / s ≤
        ((1 + ε) * (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal) / s :=
  ⟨fun h => div_le_div_of_nonneg_right h hs.le,
    fun h => (div_le_div_iff_of_pos_right hs).mp h⟩

end LeanFormal.IUT.XiFPaper.Mzk1StepXICorrectedRegionGap1Actual

end
