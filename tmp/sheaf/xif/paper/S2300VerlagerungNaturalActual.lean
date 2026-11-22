import tmp.sheaf.xif.paper.S2292TransferCompatActual
import tmp.sheaf.xif.paper.S2200TransferNaturalityActual
import tmp.sheaf.xif.paper.S2179StageConjEquivActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2300VerlagerungNaturalActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2000CohomologicalPsiCnsActual
open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual
open LeanFormal.IUT.XiFPaper.S2179StageConjEquivActual
open LeanFormal.IUT.XiFPaper.S2027LocalArtinActual
open LeanFormal.IUT.XiFPaper.S2169MuQZConjugationActual
open LeanFormal.IUT.XiFPaper.S2200TransferNaturalityActual
open LeanFormal.IUT.XiFPaper.S2292TransferCompatActual

variable (p : Nat) [Fact (Nat.Prime p)]

/-- Exact coercion missing: subgroupOf commutes with the conjugation
equivalence of open subgroups. -/
def S2300SubgroupOfMapRequired : Prop :=
  ∀ (g : Gv p) (H K : Index p) (h : H ≤ K),
    ((H.toSubgroup.subgroupOf K.toSubgroup).map
        (S2200ConjEquiv p g K).toMonoidHom) =
      (S2169ConjIndex p g H).toSubgroup.subgroupOf
        (S2169ConjIndex p g K).toSubgroup

/-- Exact verlagerungOpen naturality square. -/
def S2300VerlagerungNaturalRequired : Prop :=
  ∀ (g : Gv p) (H K : Index p) (h : H ≤ K),
    ∃ h' : S2169ConjIndex p g H ≤ S2169ConjIndex p g K,
      (Abelianization.map (S2200ConjEquiv p g H).toMonoidHom).comp
          (verlagerungOpen p h) =
        (verlagerungOpen p h').comp
          (Abelianization.map (S2200ConjEquiv p g K).toMonoidHom)

/-- Exact S2179 stage compatibility target. -/
abbrev S2300StageCompatibleRequired : Prop :=
  S2179TransferCompatible (p := p)

#check S2300SubgroupOfMapRequired
#check S2300VerlagerungNaturalRequired
#check S2300StageCompatibleRequired

end LeanFormal.IUT.XiFPaper.S2300VerlagerungNaturalActual

end