import tmp.sheaf.xif.paper.S2346VerlagerungFinalComposeActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2347FinalComposeCastActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2000CohomologicalPsiCnsActual
open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual
open LeanFormal.IUT.XiFPaper.S2027LocalArtinActual
open LeanFormal.IUT.XiFPaper.S2169MuQZConjugationActual
open LeanFormal.IUT.XiFPaper.S2300VerlagerungNaturalActual
open LeanFormal.IUT.XiFPaper.S2179StageConjEquivActual

variable (p : Nat) [Fact (Nat.Prime p)]

abbrev S2347VerlagerungNaturalRequired : Prop :=
  S2300VerlagerungNaturalRequired (p := p)

abbrev S2347StageCompatibleRequired : Prop :=
  S2179TransferCompatible (p := p)

#check S2347VerlagerungNaturalRequired
#check S2347StageCompatibleRequired

end LeanFormal.IUT.XiFPaper.S2347FinalComposeCastActual

end