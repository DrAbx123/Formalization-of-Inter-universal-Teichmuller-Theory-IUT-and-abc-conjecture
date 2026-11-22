import tmp.sheaf.xif.paper.Mzk1StepXIGreenRouteActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # StepXI green route consumer; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIGreenRouteConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1StepXIGreenRouteActual

theorem stepXIGreenRouteConsumer_bundle
    (S : LeanFormal.IUT.XiFPaper.Mzk1StepXIContractConstructionActual.StepXIContractSourceData) :
    Cor312Conclusion (LeanFormal.IUT.XiFPaper.Mzk1StepXIContractConstructionActual.StepXIContractSourceData.toContract S) ∧
      LeanFormal.IUT.Audit.ipl.id = "IUT-III.IPL" :=
  have h := stepXIGreenRoute_bundle S
  ⟨h.1, h.2.2.1⟩

def stepXIGreenRouteConsumerRows : List (String × String × String) :=
  [ ("contract + route bundle", "PROVED", "stepXIGreenRouteConsumer_bundle") ]

theorem stepXIGreenRouteConsumerRows_length : stepXIGreenRouteConsumerRows.length = 1 := rfl

#check stepXIGreenRouteConsumer_bundle
#check stepXIGreenRouteConsumerRows_length

end LeanFormal.IUT.XiFPaper.Mzk1StepXIGreenRouteConsumerActual
end