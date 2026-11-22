import tmp.sheaf.xif.paper.Mzk1StepXIABCTwoGapsFormalActual
import tmp.sheaf.xif.paper.Mzk1StepXIS1902BridgeWiringActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi A618 audit proofs

Proof-level counterparts of the machine audit: the audited constants are re-exported
with their actual proofs (no axioms added). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIAuditProofActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1StepXIABCTwoGapsFormalActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIS1902BridgeWiringActual

theorem stepxi_audit_twoGaps_ABC (I : StepXIABCTwoGaps) : ABCConjecture :=
  stepxi_twoGaps_ABC I

theorem stepxi_audit_bridge_heightBound (X : Type) (W : IQHullLogVolumeInterface X)
    (logShellPoint : Nat → Nat → Nat → X)
    (I : StepXIBridgeFamily X W logShellPoint) :
    ∀ ε : Real, 0 < ε → ∃ A : Real,
      ∀ a b c : Nat, IsABCTriple a b c →
        Height.logHeight₁ (abcRationalPoint a c) <=
          (1 + ε) * arithmeticWeight (abcRationalPoint a c) + A :=
  stepxiBridge_heightBound X W logShellPoint I

end LeanFormal.IUT.XiFPaper.Mzk1StepXIAuditProofActual

end
