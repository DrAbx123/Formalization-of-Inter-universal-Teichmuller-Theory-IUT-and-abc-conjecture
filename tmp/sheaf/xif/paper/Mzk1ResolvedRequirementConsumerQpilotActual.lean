/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1ResolvedRequirementAcceptanceQpilotActual
import tmp.sheaf.xif.paper.Mzk1SignedCor312ContractActual
import Mathlib.Tactic

/-! # Mzk1ResolvedRequirementConsumerQpilotActual — consumers of resolved acceptance

A588 (qpilot lane): consumer forms of the resolved requirement acceptance:
the signed inequality and the contract's target-vs-q content. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1ResolvedRequirementConsumerQpilotActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual
open LeanFormal.IUT.XiFPaper.Mzk1ResolvedRequirementAcceptanceQpilotActual
open LeanFormal.IUT.XiFPaper.Mzk1SignedCor312ContractActual

variable {α : Type*} {vol : Set α → Real}

/-- Consumer: resolved acceptance gives the strict signed inequality. -/
theorem resolved_strict_signed (D : XiEContainmentRequirement α vol) :
    requirementSignedQ D < requirementSignedTheta D :=
  (resolvedRequirementAcceptance D).strict_signed

/-- Consumer: resolved acceptance gives the non-strict signed inequality. -/
theorem resolved_signed_inequality (D : XiEContainmentRequirement α vol) :
    requirementSignedQ D ≤ requirementSignedTheta D :=
  (resolvedRequirementAcceptance D).signed_inequality

/-- Consumer: resolved acceptance gives the contract's Cor 3.12 conclusion. -/
theorem resolved_contract_cor312 (D : XiEContainmentRequirement α vol)
    (hqneg : requirementSignedQ D < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion (requirementContract D hqneg ipl hipl she hshe apt hapt) :=
  (resolvedRequirementAcceptance D).contract_cor312 hqneg ipl hipl she hshe apt hapt

/-- Consumer: resolved acceptance's C_Θ ≥ −1 form (real-level). -/
theorem resolved_CTheta {qMag C thetaLog qLog : Real}
    (hq : 0 < qMag) (hqeq : qLog = -qMag) (hC : thetaLog = C * qMag)
    (hineq : qLog ≤ thetaLog) : -1 ≤ C := by
  rw [hqeq, hC] at hineq
  nlinarith

#check resolved_contract_cor312
#check resolved_CTheta

end LeanFormal.IUT.XiFPaper.Mzk1ResolvedRequirementConsumerQpilotActual
end
