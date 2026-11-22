/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface
import tmp.sheaf.xif.paper.Mzk1ABCEstimatesArithmeticQpilotActual
import Mathlib.Tactic

/-! # Mzk1ScalingElementAuditQpilotActual — scaling element audit + Gap1 full ratio

A657 (qpilot lane):
* audit of the candidate scaling element `λ = a+b+c+1` (positive, `≥ 1`: expanding,
  unlike the paper's contracting `q`-type scaling; recorded as an audit row);
* Gap-1 full-ratio theorem-ization: the height comparison is equivalent to the
  ratio bound `h/v ≤ 1+ε` for positive region volume `v`. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.Mzk1ScalingElementAuditQpilotActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1ABCEstimatesArithmeticQpilotActual

/-- The candidate triple-dependent scaling element `a+b+c+1`. -/
def tripleScaleElement (a b c : Nat) : Nat := a + b + c + 1

theorem tripleScaleElement_pos (a b c : Nat) : 0 < tripleScaleElement a b c :=
  Nat.succ_pos _

theorem tripleScaleElement_ge_one (a b c : Nat) : 1 ≤ tripleScaleElement a b c :=
  Nat.succ_le_succ (Nat.zero_le _)

theorem tripleScaleElement_cast_pos (a b c : Nat) :
    (0 : Real) < (tripleScaleElement a b c : Real) := by
  exact_mod_cast tripleScaleElement_pos a b c

theorem tripleScaleElement_cast_ge_one (a b c : Nat) :
    (1 : Real) ≤ (tripleScaleElement a b c : Real) := by
  exact_mod_cast tripleScaleElement_ge_one a b c

/-- The candidate scaling is expanding (`λ ≥ 1`), unlike a contracting `q`-type
scaling (`‖q‖ < 1`); audit row. -/
theorem tripleScaleElement_expanding (a b c : Nat) :
    (1 : Real) ≤ (tripleScaleElement a b c : Real) :=
  tripleScaleElement_cast_ge_one a b c

/-- Gap-1 ratio bound: from `h ≤ (1+ε)v` with `v > 0` derive `h/v ≤ 1+ε`. -/
theorem gap1_ratio_bound {h v epsilon : Real} (hv : 0 < v)
    (h1 : h ≤ (1 + epsilon) * v) :
    h / v ≤ 1 + epsilon :=
  (div_le_iff₀ hv).mpr h1

/-- Gap-1 full-ratio theorem-ization: the comparison is exactly the ratio bound;
conversely the ratio bound gives the comparison. -/
theorem gap1_full_ratio_iff {h v epsilon : Real} (hv : 0 < v) :
    (h ≤ (1 + epsilon) * v) ↔ (h / v ≤ 1 + epsilon) :=
  ⟨fun h1 => gap1_ratio_bound hv h1,
   fun h1 => (div_le_iff₀ hv).mp h1⟩

/-- Gap-1 full ratio on a bridge comparison datum with positive region volume. -/
theorem gap1_full_ratio_of_bridge {X : Type} {W : IQHullLogVolumeInterface X}
    {epsilon : Real} (C : Cor312EpsilonArithmeticComparison W epsilon)
    {a b c : Nat} (habc : IsABCTriple a b c)
    (hv : 0 < (W.logVolume (C.comparisonRegion a b c)).toReal) :
    Height.logHeight₁ (abcRationalPoint a c) /
        (W.logVolume (C.comparisonRegion a b c)).toReal ≤ 1 + epsilon :=
  gap1_ratio_bound hv (C.height_le_normalizedRegionVolume a b c habc)

/-- Audit rows for the scaling element / Gap-1 ratio. -/
def scalingElementRows : List (String × String) :=
  [ ("tripleScaleElement = a+b+c+1", "DEFINED (positive, >= 1)"),
    ("expanding scaling (lambda >= 1)", "PROVED (audit: not q-contracting)"),
    ("Gap1 ratio bound h/v <= 1+eps", "PROVED (v > 0)"),
    ("Gap1 full-ratio iff", "PROVED"),
    ("Gap1 ratio on bridge datum", "PROVED (conditional on v > 0)") ]

theorem scalingElementRows_length : scalingElementRows.length = 5 := rfl

#check gap1_full_ratio_iff
#check gap1_full_ratio_of_bridge
#check scalingElementRows_length

end LeanFormal.IUT.XiFPaper.Mzk1ScalingElementAuditQpilotActual
end
