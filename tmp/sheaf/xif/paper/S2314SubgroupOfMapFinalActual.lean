import tmp.sheaf.xif.paper.S2311OpenComapActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2314SubgroupOfMapFinalActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2000CohomologicalPsiCnsActual
open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual
open LeanFormal.IUT.XiFPaper.S2027LocalArtinActual
open LeanFormal.IUT.XiFPaper.S2169MuQZConjugationActual
open LeanFormal.IUT.XiFPaper.S2300VerlagerungNaturalActual
open LeanFormal.IUT.XiFPaper.S2311OpenComapActual

variable (p : Nat) [Fact (Nat.Prime p)]

abbrev S2314SubgroupOfMapRequired : Prop :=
  S2300SubgroupOfMapRequired (p := p)

#check S2314SubgroupOfMapRequired

end LeanFormal.IUT.XiFPaper.S2314SubgroupOfMapFinalActual

end