import tmp.sheaf.xif.paper.Mzk1StepXIContractConstructionActual
import tmp.sheaf.xif.paper.Mzk1IUTIIILinkActual
import tmp.sheaf.xif.paper.Mzk1Cor312ObligationConsumerActual
import LeanFormal.IUT.IUTIII.Corollary312.Routes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # StepXI green all-in-one consumer; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIGreenAllActual

open LeanFormal.IUT
open LeanFormal.IUT.Audit
open LeanFormal.IUT.XiFPaper.Mzk1StepXIContractConstructionActual
open LeanFormal.IUT.XiFPaper.Mzk1IUTIIILinkActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312ObligationConsumerActual

theorem stepXIGreenAll_cor312 (S : StepXIContractSourceData) (L : IUTIIToStepXILink) :
    Cor312Conclusion S.toContract ∧ Cor312Conclusion L.toContract :=
  ⟨sourceData_cor312 S, cor312Conclusion_of_IUTIIToStepXILink L⟩

theorem stepXIGreenAll_qpositive (S : StepXIContractSourceData) (L : IUTIIToStepXILink) :
    0 < -S.toContract.qSigned ∧ 0 < -L.toContract.qSigned :=
  ⟨sourceData_q_positive S, q_positive_of_IUTIIToStepXILink L⟩

theorem stepXIGreenAll_obligations :
    ipl.id = "IUT-III.IPL" ∧ she.id = "IUT-III.SHE" ∧ apt.id = "IUT-III.APT" :=
  ⟨ipl_id, she_id, apt_id⟩

theorem stepXIGreenAll_bundle (S : StepXIContractSourceData) (L : IUTIIToStepXILink) :
    Cor312Conclusion S.toContract ∧ Cor312Conclusion L.toContract ∧
      ipl.id = "IUT-III.IPL" ∧ she.id = "IUT-III.SHE" ∧ apt.id = "IUT-III.APT" :=
  ⟨sourceData_cor312 S, cor312Conclusion_of_IUTIIToStepXILink L, ipl_id, she_id, apt_id⟩

def stepXIGreenAllRows : List (String × String × String) :=
  [ ("both contract kinds => Cor312", "PROVED", "stepXIGreenAll_cor312"),
    ("both q-positive", "PROVED", "stepXIGreenAll_qpositive"),
    ("obligation ids", "PROVED", "stepXIGreenAll_obligations"),
    ("bundle", "PROVED", "stepXIGreenAll_bundle") ]

theorem stepXIGreenAllRows_length : stepXIGreenAllRows.length = 4 := rfl

#check stepXIGreenAll_bundle
#check stepXIGreenAllRows_length

end LeanFormal.IUT.XiFPaper.Mzk1StepXIGreenAllActual
end