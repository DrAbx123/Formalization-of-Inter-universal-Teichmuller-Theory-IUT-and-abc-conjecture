import tmp.sheaf.xif.paper.Mzk1IUTIIILinkConsumerActual
import tmp.sheaf.xif.paper.Mzk1StepXIConsumerBundleActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # IUTIII green link+StepXI bundle; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1IUTIIIGreenLinkStepXIActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1StepXIConsumerBundleActual

theorem iutiiiGreen_bundle (S : LeanFormal.IUT.XiFPaper.Mzk1StepXIContractConstructionActual.StepXIContractSourceData) :
    Cor312Conclusion (LeanFormal.IUT.XiFPaper.Mzk1StepXIContractConstructionActual.StepXIContractSourceData.toContract S) ∧
      LeanFormal.IUT.Audit.ipl.id = "IUT-III.IPL" ∧
      LeanFormal.IUT.Audit.she.id = "IUT-III.SHE" ∧
      LeanFormal.IUT.Audit.apt.id = "IUT-III.APT" :=
  have h := stepXI_bundle S
  ⟨h.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩

def iutiiiGreenRows : List (String × String × String) :=
  [ ("StepXI consumer bundle", "PROVED", "iutiiiGreen_bundle") ]

theorem iutiiiGreenRows_length : iutiiiGreenRows.length = 1 := rfl

#check iutiiiGreen_bundle
#check iutiiiGreenRows_length

end LeanFormal.IUT.XiFPaper.Mzk1IUTIIIGreenLinkStepXIActual
end