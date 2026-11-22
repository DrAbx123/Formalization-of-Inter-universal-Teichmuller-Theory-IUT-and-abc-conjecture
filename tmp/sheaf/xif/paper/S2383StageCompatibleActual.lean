import tmp.sheaf.xif.paper.S2371HnatExplicitActual
import tmp.sheaf.xif.paper.S2179StageConjEquivActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2383StageCompatibleActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2000CohomologicalPsiCnsActual
open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual
open LeanFormal.IUT.XiFPaper.S2027LocalArtinActual
open LeanFormal.IUT.XiFPaper.S2169MuQZConjugationActual
open LeanFormal.IUT.XiFPaper.S2179StageConjEquivActual

variable (p : Nat) [Fact (Nat.Prime p)]

abbrev S2383StageCompatibleRequired : Prop :=
  S2179TransferCompatible (p := p)

#check S2383StageCompatibleRequired

end LeanFormal.IUT.XiFPaper.S2383StageCompatibleActual

end