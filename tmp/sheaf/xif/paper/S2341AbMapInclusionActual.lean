import tmp.sheaf.xif.paper.S2338TransferCompatDoneActual
import tmp.sheaf.xif.paper.S2317SubgroupOfApplyActual
import tmp.sheaf.xif.paper.S2200TransferNaturalityActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2341AbMapInclusionActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2000CohomologicalPsiCnsActual
open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual
open LeanFormal.IUT.XiFPaper.S2027LocalArtinActual
open LeanFormal.IUT.XiFPaper.S2169MuQZConjugationActual
open LeanFormal.IUT.XiFPaper.S2317SubgroupOfApplyActual
open LeanFormal.IUT.XiFPaper.S2338TransferCompatDoneActual
open LeanFormal.IUT.XiFPaper.S2200TransferNaturalityActual

variable (p : Nat) [Fact (Nat.Prime p)]

theorem S2341_abmap_inclusion (g : Gv p) (H K : Index p) (h : H ≤ K) :
    let h' := S2338_conjIndex_mono p g h
    let eH := (S2200ConjEquiv p g H).toMonoidHom
    let eK := (S2200ConjEquiv p g K).toMonoidHom
    let Hsub := H.toSubgroup.subgroupOf K.toSubgroup
    let hcast := S2317_subgroupOf_map p g H K h
    let eHsub := (Subgroup.equivMapOfInjective Hsub eK
      (S2200ConjEquiv p g K).injective).trans (MulEquiv.subgroupCongr hcast)
    (Abelianization.map eH).comp
        (Abelianization.map (Subgroup.subgroupOfEquivOfLe h).toMonoidHom) =
      (Abelianization.map (Subgroup.subgroupOfEquivOfLe h').toMonoidHom).comp
        (Abelianization.map eHsub.toMonoidHom) := by
  dsimp only
  apply Abelianization.hom_ext
  ext x
  simp only [MonoidHom.comp_apply, Abelianization.map_of]
  congr 1

#check S2341_abmap_inclusion
#print axioms S2341_abmap_inclusion

end LeanFormal.IUT.XiFPaper.S2341AbMapInclusionActual

end