import tmp.sheaf.xif.paper.Mzk1StepXIGreenConsumerActual
import tmp.sheaf.xif.paper.Mzk1StepXIContractConstructionActual
import tmp.sheaf.xif.paper.Mzk1Cor312ObligationConsumerActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # Mzk1HullStepXIPaperAssetsConsumerActualAdapted — StepXI paper-assets consumer batch

A473: real Lean consumer batch over the green StepXI construction/obligation
files. No sorry/axioms; no closure claim. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1HullStepXIPaperAssetsConsumerActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.Audit
open LeanFormal.IUT.XiFPaper.Mzk1StepXIContractConstructionActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312ObligationConsumerActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIGreenConsumerActual

theorem stepXIPaperAssets_contract (S : StepXIContractSourceData) :
    Cor312Conclusion S.toContract := sourceData_cor312 S

theorem stepXIPaperAssets_qpositive (S : StepXIContractSourceData) :
    0 < -S.toContract.qSigned := sourceData_q_positive S

theorem stepXIPaperAssets_obligations :
    ipl.id = "IUT-III.IPL" ∧ she.id = "IUT-III.SHE" ∧ apt.id = "IUT-III.APT" :=
  ⟨ipl_id, she_id, apt_id⟩

def stepXIPaperAssetsRows : List (String × String × String) :=
  [ ("contract -> Cor312", "PROVED", "stepXIPaperAssets_contract"),
    ("q-positive", "PROVED", "stepXIPaperAssets_qpositive"),
    ("obligations", "PROVED", "stepXIPaperAssets_obligations") ]

theorem stepXIPaperAssetsRows_length : stepXIPaperAssetsRows.length = 3 := rfl

#check stepXIPaperAssets_contract
#check stepXIPaperAssetsRows_length

end LeanFormal.IUT.XiFPaper.Mzk1HullStepXIPaperAssetsConsumerActualAdapted
end