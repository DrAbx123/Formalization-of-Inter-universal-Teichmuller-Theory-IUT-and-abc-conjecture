import tmp.sheaf.xif.paper.Mzk1StepXIContractConstructionActual
import tmp.sheaf.xif.paper.Mzk1TreeIndeterminacyFactsActual
import LeanFormal.IUT.IUTIII.Corollary312.Routes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-!
# STEP 0 prior-art: StepXI construction x Ind facts -> Mzk1StepXIContractConstructionActual (sourceData->contract->Cor312/q-positive/route) + Mzk1TreeIndeterminacyFactsActual (Ind ids/statuses) + Routes -> PROVED joint: from one source datum get Cor312, q-positive, route certificate for all three routes, and the pending Ind obligation ids/statuses. No new math; no closure.

# Mzk1StepXIConstructionIndJointActual — StepXI construction + Ind obligations joint

PROVED:
* `stepXI_ind_joint`: Cor312 + q-positive + all-route certificates + Ind ids/statuses
  from one StepXIContractSourceData.
Registry frozen 14041.  No closure claim.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIConstructionIndJointActual

open LeanFormal.IUT
open LeanFormal.IUT.Audit
open LeanFormal.IUT.XiFPaper.Mzk1StepXIContractConstructionActual
open LeanFormal.IUT.XiFPaper.Mzk1TreeIndeterminacyFactsActual

/-- **PROVED (joint bundle):** contract conclusions + all route certificates + Ind facts. -/
theorem stepXI_ind_joint (S : StepXIContractSourceData) :
    Cor312Conclusion S.toContract ∧
      (0 < -S.toContract.qSigned) ∧
      Cor312Conclusion (sourceData_routeCertificate Cor312Route.mochizuki3115 S).contract ∧
      Cor312Conclusion (sourceData_routeCertificate Cor312Route.arithmeticTeichmuller S).contract ∧
      Cor312Conclusion (sourceData_routeCertificate Cor312Route.sarkisyanErdosKac S).contract ∧
      ind1.id = "IUT-III.Ind1" ∧ ind2.id = "IUT-III.Ind2" ∧
      ind3.id = "IUT-III.Ind3" :=
  ⟨sourceData_cor312 S, sourceData_q_positive S,
    sourceData_routeCertificate_conclusion _ S,
    sourceData_routeCertificate_conclusion _ S,
    sourceData_routeCertificate_conclusion _ S,
    ind1_id, ind2_id, ind3_id⟩

def stepXIIndJointRows : List (String × String × String) :=
  [ ("Cor312 + q-positive from source data", "PROVED", "sourceData_cor312 / sourceData_q_positive")
  , ("all three route certificates", "PROVED", "sourceData_routeCertificate_conclusion")
  , ("Ind obligation ids", "PROVED", "ind1_id/ind2_id/ind3_id (tree records)")
  , ("Ind obligations proof", "NAMED (tree pending)", "recorded pending; proved kernels in Ind* files") ]

theorem stepXIIndJointRows_length : stepXIIndJointRows.length = 4 := rfl

#check stepXI_ind_joint
#check stepXIIndJointRows_length

end LeanFormal.IUT.XiFPaper.Mzk1StepXIConstructionIndJointActual
end