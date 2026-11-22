/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface
import Mathlib.Tactic

/-! # Mzk1ABCEntryQpilotActual — ABC entry consumer (qpilot lane, own name)

A572: entry theorems for the Cor 3.12 -> ABC/height bridge, re-exported from the
green `Cor312ToABCBridgeInterface`.  The two comparison gaps stay named fields of
the bridge data; no closure is claimed.
 -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1ABCEntryQpilotActual

open LeanFormal.IUT
open LeanFormal.IUT

/-- ABC entry: the bridge interface gives the height bound (named gaps as data). -/
theorem abcEntry_heightBound (D : Cor312ToABCBridgeInterface) :
    ∀ epsilon : Real, 0 < epsilon → ∃ A : Real,
      ∀ a b c : Nat, IsABCTriple a b c →
        Height.logHeight₁ (abcRationalPoint a c) ≤
          (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) + A :=
  cor312ToABCBridge_heightBound D

/-- ABC entry: the bridge interface gives `ABCConjecture` (conditional closure). -/
theorem abcEntry_abcConjecture (D : Cor312ToABCBridgeInterface) :
    ABCConjecture :=
  cor312ToABCBridge_abcConjecture D

/-- ABC entry: the bridge interface gives the logarithmic form. -/
theorem abcEntry_abcLogConjecture (D : Cor312ToABCBridgeInterface) :
    ABCLogConjecture :=
  cor312ToABCBridge_abcLogConjecture D

/-- ABC entry: the bridge interface gives the radical-power form. -/
theorem abcEntry_rpowBound (D : Cor312ToABCBridgeInterface) :
    ∀ epsilon : Real, 0 < epsilon → ∃ K : Real, 0 < K ∧
      ∀ a b c : Nat, IsABCTriple a b c →
        (c : Real) ≤ K * (radical (a * b * c) : Real) ^ (1 + epsilon) :=
  cor312ToABCBridge_rpowBound D

/-- ABC entry: interface inhabitation is equivalent to `ABCConjecture`. -/
theorem abcEntry_nonempty_iff :
    Nonempty Cor312ToABCBridgeInterface.{0} ↔ ABCConjecture :=
  cor312ToABCBridgeInterface_nonempty_iff_abcConjecture

#check abcEntry_heightBound
#check abcEntry_abcConjecture

end LeanFormal.IUT.XiFPaper.Mzk1ABCEntryQpilotActual
end
