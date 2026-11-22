import tmp.sheaf.xif.paper.Mzk1StepXIGreenRouteActual
import tmp.sheaf.xif.paper.Mzk1StepXIContractConstructionActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # StepXI green route consumer 2; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIGreenRouteConsumer2ActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1StepXIGreenRouteActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIContractConstructionActual

theorem stepXIGreenRouteConsumer2_bundle (S : StepXIContractSourceData) :
    Cor312Conclusion S.toContract :=
  (stepXIGreenRoute_bundle S).1

def stepXIGreenRouteConsumer2Rows : List (String × String × String) :=
  [ ("Cor312 projection", "PROVED", "stepXIGreenRouteConsumer2_bundle") ]

theorem stepXIGreenRouteConsumer2Rows_length : stepXIGreenRouteConsumer2Rows.length = 1 := rfl

#check stepXIGreenRouteConsumer2_bundle
#check stepXIGreenRouteConsumer2Rows_length

end LeanFormal.IUT.XiFPaper.Mzk1StepXIGreenRouteConsumer2ActualAdapted
end