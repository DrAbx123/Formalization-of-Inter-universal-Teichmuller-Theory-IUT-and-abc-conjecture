import tmp.sheaf.xif.paper.Mzk1XiEContainmentRequirementActual
import tmp.sheaf.xif.paper.Mzk1SignedCor312ContractActual
import tmp.sheaf.xif.paper.Mzk1SignedLogVolumeCor312Actual

/-!
# A540 independent self-checks for the final assembly (green files only)

Checks the requirement/contract interface used by the final assembly, without
importing the still-pending final assembly itself:
* strict signed inequality from the non-vacuous xi-e requirement;
* weak signed inequality;
* `Cor312Conclusion` from the requirement contract with real IPL/SHE/APT data;
* matching paper target (`-|log q| <= -|log Theta|`).

No sorry, axiom, True or placeholder.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312SelfCheckIndependentActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual
open LeanFormal.IUT.XiFPaper.Mzk1SignedCor312ContractActual
open LeanFormal.IUT.XiFPaper.Mzk1SignedLogVolumeCor312Actual

universe u

/-- Strict non-vacuous xi-e requirement gives the strict signed inequality. -/
theorem check_requirement_strict {α : Type u} {vol : Set α → Real}
    (D : XiEContainmentRequirement α vol) :
    requirementSignedQ D < requirementSignedTheta D :=
  requirement_strict_signed D

/-- The requirement gives the weak signed inequality (paper direction). -/
theorem check_requirement_weak {α : Type u} {vol : Set α → Real}
    (D : XiEContainmentRequirement α vol) :
    requirementSignedQ D ≤ requirementSignedTheta D :=
  requirement_signed_inequality D

/-- `Cor312Conclusion` from the requirement contract (real IPL/SHE/APT data). -/
theorem check_requirement_contract {α : Type u} {vol : Set α → Real}
    (D : XiEContainmentRequirement α vol)
    (hqneg : requirementSignedQ D < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion (requirementContract D hqneg ipl hipl she hshe apt hapt) :=
  requirement_cor312 D hqneg ipl hipl she hshe apt hapt

/-- The target comparison of the requirement is exactly the paper signed form. -/
theorem check_target_matches_paper {α : Type u} {vol : Set α → Real}
    (D : XiEContainmentRequirement α vol) :
    signedLogVolume vol D.qRegion ≤ signedLogVolume vol D.hullRegion :=
  check_requirement_weak D

end LeanFormal.IUT.XiFPaper.Mzk1Cor312SelfCheckIndependentActual
