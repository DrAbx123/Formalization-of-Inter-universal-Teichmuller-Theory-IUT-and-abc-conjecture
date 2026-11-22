import tmp.sheaf.xif.paper.S2336TransferCompActual
import tmp.sheaf.xif.paper.S2317SubgroupOfApplyActual
import tmp.sheaf.xif.paper.S2300VerlagerungNaturalActual
import tmp.sheaf.xif.paper.S2179StageConjEquivActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2338TransferCompatDoneActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2000CohomologicalPsiCnsActual
open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual
open LeanFormal.IUT.XiFPaper.S2027LocalArtinActual
open LeanFormal.IUT.XiFPaper.S2169MuQZConjugationActual
open LeanFormal.IUT.XiFPaper.S2336TransferCompActual
open LeanFormal.IUT.XiFPaper.S2300VerlagerungNaturalActual
open LeanFormal.IUT.XiFPaper.S2179StageConjEquivActual

variable (p : Nat) [Fact (Nat.Prime p)]

theorem S2338_conjIndex_mono (g : Gv p) {H K : Index p} (h : H ≤ K) :
    S2169ConjIndex p g H ≤ S2169ConjIndex p g K := by
  intro x hx
  simpa [S2169ConjIndex] using
    (Subgroup.comap_mono (f := (MulAut.conj g).toMonoidHom) h hx)

abbrev S2338VerlagerungNaturalRequired : Prop :=
  S2300VerlagerungNaturalRequired (p := p)

abbrev S2338StageCompatibleRequired : Prop :=
  S2179TransferCompatible (p := p)

#check S2338_conjIndex_mono
#check S2338VerlagerungNaturalRequired
#check S2338StageCompatibleRequired
#print axioms S2338_conjIndex_mono

end LeanFormal.IUT.XiFPaper.S2338TransferCompatDoneActual

end