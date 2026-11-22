import tmp.sheaf.xif.paper.Mzk1StepXIObligationRouteJointActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # StepXI obligation-route green consumer; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIObligationRouteGreenActual

open LeanFormal.IUT
open LeanFormal.IUT.Audit
open LeanFormal.IUT.XiFPaper.Mzk1StepXIObligationRouteJointActual

theorem stepXIObRouteGreen_bundle (S : LeanFormal.IUT.XiFPaper.Mzk1StepXIContractConstructionActual.StepXIContractSourceData) :
    Cor312Conclusion (LeanFormal.IUT.XiFPaper.Mzk1StepXIContractConstructionActual.StepXIContractSourceData.toContract S) ∧
      ipl.id = "IUT-III.IPL" :=
  have h := stepXIObligationRoute_bundle S
  ⟨h.1, h.2.2.1⟩

def stepXIObRouteGreenRows : List (String × String × String) :=
  [ ("construction + obligation bundle", "PROVED", "stepXIObRouteGreen_bundle") ]

theorem stepXIObRouteGreenRows_length : stepXIObRouteGreenRows.length = 1 := rfl

#check stepXIObRouteGreen_bundle
#check stepXIObRouteGreenRows_length

end LeanFormal.IUT.XiFPaper.Mzk1StepXIObligationRouteGreenActual
end