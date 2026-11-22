import tmp.sheaf.xif.paper.S2317SubgroupOfApplyActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2334VerlagerungEqActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2000CohomologicalPsiCnsActual
open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual
open LeanFormal.IUT.XiFPaper.S2027LocalArtinActual
open LeanFormal.IUT.XiFPaper.S2169MuQZConjugationActual
open LeanFormal.IUT.XiFPaper.S2292TransferCompatActual

variable (p : Nat) [Fact (Nat.Prime p)]

/-- Exact missing: verlagerungOpen as composition with transferAb. -/
def S2334VerlagerungOpenEqRequired : Prop :=
  ∀ (H K : Index p) (h : H ≤ K) [Subgroup.FiniteIndex H.toSubgroup],
    verlagerungOpen p h =
      (Abelianization.map (Subgroup.subgroupOfEquivOfLe h).toMonoidHom).comp
        (Verlagerung.transferAb (H.toSubgroup.subgroupOf K.toSubgroup))

#check S2334VerlagerungOpenEqRequired

end LeanFormal.IUT.XiFPaper.S2334VerlagerungEqActual

end