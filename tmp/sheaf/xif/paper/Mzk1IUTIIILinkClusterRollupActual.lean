import tmp.sheaf.xif.paper.Mzk1IUTIIILinkConsumerActual
import tmp.sheaf.xif.paper.Mzk1IUTIIILinkSourceDataGreenActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # IUTII link cluster rollup; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1IUTIIILinkClusterRollupActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1IUTIIILinkActual
open LeanFormal.IUT.XiFPaper.Mzk1IUTIIILinkConsumerActual
open LeanFormal.IUT.XiFPaper.Mzk1IUTIIILinkSourceDataGreenActual

theorem iutiiiLinkClusterRollup_bundle (L : IUTIIToStepXILink) :
    Cor312Conclusion L.toContract ∧
      Cor312Conclusion (linkSourceDataGreen L).toContract :=
  ⟨cor312Conclusion_of_IUTIIToStepXILink L, iutiiiLinkSourceDataGreen_cor312 L⟩

def iutiiiLinkClusterRollupRows : List (String × String × String) :=
  [ ("link contract + source data contract", "PROVED", "iutiiiLinkClusterRollup_bundle") ]

theorem iutiiiLinkClusterRollupRows_length : iutiiiLinkClusterRollupRows.length = 1 := rfl

#check iutiiiLinkClusterRollup_bundle
#check iutiiiLinkClusterRollupRows_length

end LeanFormal.IUT.XiFPaper.Mzk1IUTIIILinkClusterRollupActual
end