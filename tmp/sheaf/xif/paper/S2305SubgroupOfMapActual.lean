import tmp.sheaf.xif.paper.S2300VerlagerungNaturalActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2305SubgroupOfMapActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2000CohomologicalPsiCnsActual
open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual
open LeanFormal.IUT.XiFPaper.S2027LocalArtinActual
open LeanFormal.IUT.XiFPaper.S2169MuQZConjugationActual
open LeanFormal.IUT.XiFPaper.S2300VerlagerungNaturalActual

variable (p : Nat) [Fact (Nat.Prime p)]

abbrev S2305SubgroupOfMapRequired : Prop :=
  S2300SubgroupOfMapRequired (p := p)

#check S2305SubgroupOfMapRequired

end LeanFormal.IUT.XiFPaper.S2305SubgroupOfMapActual

end