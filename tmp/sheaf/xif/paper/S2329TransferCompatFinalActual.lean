import tmp.sheaf.xif.paper.S2317SubgroupOfApplyActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2329TransferCompatFinalActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2000CohomologicalPsiCnsActual
open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual
open LeanFormal.IUT.XiFPaper.S2027LocalArtinActual
open LeanFormal.IUT.XiFPaper.S2169MuQZConjugationActual
open LeanFormal.IUT.XiFPaper.S2300VerlagerungNaturalActual
open LeanFormal.IUT.XiFPaper.S2317SubgroupOfApplyActual

variable (p : Nat) [Fact (Nat.Prime p)]

abbrev S2329VerlagerungNaturalRequired : Prop :=
  S2300VerlagerungNaturalRequired (p := p)

abbrev S2329StageCompatibleRequired : Prop :=
  S2300StageCompatibleRequired (p := p)

#check S2329VerlagerungNaturalRequired
#check S2329StageCompatibleRequired

end LeanFormal.IUT.XiFPaper.S2329TransferCompatFinalActual

end