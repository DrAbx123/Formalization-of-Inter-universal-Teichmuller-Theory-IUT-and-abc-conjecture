import tmp.sheaf.xif.paper.Mzk1StepXIConsumerBundleActual
import tmp.sheaf.xif.paper.Mzk1Cor312ObligationConsumerActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # StepXI green obligation consumer; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIGreenObligationConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.Audit
open LeanFormal.IUT.XiFPaper.Mzk1StepXIConsumerBundleActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312ObligationConsumerActual

theorem stepXIGreenObligationConsumer_bundle
    (S : LeanFormal.IUT.XiFPaper.Mzk1StepXIContractConstructionActual.StepXIContractSourceData) :
    Cor312Conclusion (LeanFormal.IUT.XiFPaper.Mzk1StepXIContractConstructionActual.StepXIContractSourceData.toContract S) ∧
      ipl.id = "IUT-III.IPL" ∧ she.id = "IUT-III.SHE" ∧ apt.id = "IUT-III.APT" :=
  ⟨stepXI_bundle S |>.1, ipl_id, she_id, apt_id⟩

def stepXIGreenObligationConsumerRows : List (String × String × String) :=
  [ ("contract + obligation ids", "PROVED", "stepXIGreenObligationConsumer_bundle") ]

theorem stepXIGreenObligationConsumerRows_length : stepXIGreenObligationConsumerRows.length = 1 := rfl

#check stepXIGreenObligationConsumer_bundle
#check stepXIGreenObligationConsumerRows_length

end LeanFormal.IUT.XiFPaper.Mzk1StepXIGreenObligationConsumerActual
end