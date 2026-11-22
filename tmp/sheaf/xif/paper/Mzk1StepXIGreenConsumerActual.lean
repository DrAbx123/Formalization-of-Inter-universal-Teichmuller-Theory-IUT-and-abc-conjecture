import tmp.sheaf.xif.paper.Mzk1StepXIContractConstructionActual
import tmp.sheaf.xif.paper.Mzk1IUTIIILinkActual
import tmp.sheaf.xif.paper.Mzk1Cor312ObligationConsumerActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # StepXI green-dep consumer (green deps only); no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIGreenConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.Audit
open LeanFormal.IUT.XiFPaper.Mzk1StepXIContractConstructionActual
open LeanFormal.IUT.XiFPaper.Mzk1IUTIIILinkActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312ObligationConsumerActual

theorem stepXIGreen_contracts (S : StepXIContractSourceData) (L : IUTIIToStepXILink) :
    Cor312Conclusion S.toContract ∧
      Cor312Conclusion L.toContract ∧
      (0 < -S.toContract.qSigned) ∧
      (0 < -L.toContract.qSigned) :=
  ⟨sourceData_cor312 S, cor312Conclusion_of_IUTIIToStepXILink L,
    sourceData_q_positive S, q_positive_of_IUTIIToStepXILink L⟩

theorem stepXIGreen_ids :
    ipl.id = "IUT-III.IPL" ∧ she.id = "IUT-III.SHE" ∧ apt.id = "IUT-III.APT" ∧
      apt.dependsOn = ["IUT-III.SHE", "IUT-II.vertical-log-kummer"] :=
  ⟨ipl_id, she_id, apt_id, apt_depends⟩

theorem stepXIGreen_bundle (S : StepXIContractSourceData) (L : IUTIIToStepXILink) :
    Cor312Conclusion S.toContract ∧ Cor312Conclusion L.toContract ∧
      ipl.id = "IUT-III.IPL" ∧ she.id = "IUT-III.SHE" ∧ apt.id = "IUT-III.APT" :=
  ⟨sourceData_cor312 S, cor312Conclusion_of_IUTIIToStepXILink L, ipl_id, she_id, apt_id⟩

def stepXIGreenRows : List (String × String × String) :=
  [ ("contracts from both source kinds", "PROVED", "stepXIGreen_contracts"),
    ("obligation ids/deps", "PROVED", "stepXIGreen_ids"),
    ("bundle", "PROVED", "stepXIGreen_bundle"),
    ("source construction / ipl/she/apt proofs", "NAMED", "tree Obligations") ]

theorem stepXIGreenRows_length : stepXIGreenRows.length = 4 := rfl

#check stepXIGreen_bundle
#check stepXIGreenRows_length

end LeanFormal.IUT.XiFPaper.Mzk1StepXIGreenConsumerActual
end