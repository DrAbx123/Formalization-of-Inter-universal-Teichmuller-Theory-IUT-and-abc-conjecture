/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface
import Mathlib.Tactic

/-! # Mzk1Gap1TheoremizationQpilotActual — Gap-1 equivalent forms (A667)

The three equivalent presentations of the Gap-1 height comparison (positive `h`,`v`):
multiplicative `h ≤ (1+ε)·v`, ratio `h/v ≤ 1+ε`, and logarithmic
`log h ≤ log(1+ε) + log v`; and their instantiation on the bridge comparison data. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Gap1TheoremizationQpilotActual

universe u

open LeanFormal.IUT
open MeasureTheory
open scoped ENNReal

/-- Multiplicative ↔ ratio form of Gap 1. -/
theorem gap1_mult_iff_ratio {h v epsilon : Real} (hv : 0 < v) :
    (h ≤ (1 + epsilon) * v) ↔ (h / v ≤ 1 + epsilon) :=
  (div_le_iff₀ hv).symm

/-- Multiplicative → logarithmic form of Gap 1. -/
theorem gap1_mult_imp_log {h v epsilon : Real} (hh : 0 < h) (hv : 0 < v)
    (heps : 0 < 1 + epsilon)
    (h1 : h ≤ (1 + epsilon) * v) :
    Real.log h ≤ Real.log (1 + epsilon) + Real.log v := by
  have hone : 0 < 1 + epsilon := heps
  calc Real.log h ≤ Real.log ((1 + epsilon) * v) := Real.log_le_log hh h1
    _ = Real.log (1 + epsilon) + Real.log v :=
        Real.log_mul (ne_of_gt hone) (ne_of_gt hv)

/-- Logarithmic → multiplicative form of Gap 1. -/
theorem gap1_log_imp_mult {h v epsilon : Real} (hh : 0 < h) (hv : 0 < v)
    (heps : 0 < 1 + epsilon)
    (hlog : Real.log h ≤ Real.log (1 + epsilon) + Real.log v) :
    h ≤ (1 + epsilon) * v := by
  have hone : 0 < 1 + epsilon := heps
  have hprod : 0 < (1 + epsilon) * v := mul_pos hone hv
  have hval : Real.log ((1 + epsilon) * v) =
      Real.log (1 + epsilon) + Real.log v :=
    Real.log_mul (ne_of_gt hone) (ne_of_gt hv)
  have : Real.log h ≤ Real.log ((1 + epsilon) * v) := by
    rw [hval]
    exact hlog
  exact (Real.log_le_log_iff hh hprod).mp this

/-- The three Gap-1 forms are equivalent (positive `h`,`v`). -/
theorem gap1_forms_iff {h v epsilon : Real} (hh : 0 < h) (hv : 0 < v)
    (heps : 0 < 1 + epsilon) :
    (h ≤ (1 + epsilon) * v) ↔
      ((h / v ≤ 1 + epsilon) ∧
        (Real.log h ≤ Real.log (1 + epsilon) + Real.log v)) := by
  constructor
  · intro h1
    exact ⟨(gap1_mult_iff_ratio hv).mp h1, gap1_mult_imp_log hh hv heps h1⟩
  · intro ⟨_, hlog⟩
    exact gap1_log_imp_mult hh hv heps hlog

/-- Gap-1 theoremization on a bridge comparison datum (positive height and region
volume): the comparison holds iff the ratio and log forms hold. -/
theorem gap1_bridge_forms {X : Type u} {W : IQHullLogVolumeInterface X}
    {epsilon : Real} (C : Cor312EpsilonArithmeticComparison W epsilon)
    {a b c : Nat} (hh : 0 < Height.logHeight₁ (abcRationalPoint a c))
    (hv : 0 < (W.logVolume (C.comparisonRegion a b c)).toReal)
    (heps : 0 < 1 + epsilon) :
    (Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + epsilon) * (W.logVolume (C.comparisonRegion a b c)).toReal) ↔
      ((Height.logHeight₁ (abcRationalPoint a c) /
          (W.logVolume (C.comparisonRegion a b c)).toReal ≤ 1 + epsilon) ∧
        (Real.log (Height.logHeight₁ (abcRationalPoint a c)) ≤
          Real.log (1 + epsilon) +
            Real.log (W.logVolume (C.comparisonRegion a b c)).toReal)) :=
  gap1_forms_iff hh hv heps

/-- Rows for the Gap-1 theoremization. -/
def gap1TheoremRows : List (String × String) :=
  [ ("mult ↔ ratio", "PROVED"),
    ("mult → log", "PROVED"),
    ("log → mult", "PROVED"),
    ("three-form equivalence", "PROVED"),
    ("bridge datum forms", "PROVED") ]

theorem gap1TheoremRows_length : gap1TheoremRows.length = 5 := rfl

#check gap1_forms_iff
#check gap1_bridge_forms
#check gap1TheoremRows_length

end LeanFormal.IUT.XiFPaper.Mzk1Gap1TheoremizationQpilotActual
end
