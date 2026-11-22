import tmp.sheaf.xif.paper.S2341AbMapInclusionActual
import tmp.sheaf.xif.paper.S2338TransferCompatDoneActual
import tmp.sheaf.xif.paper.S2292TransferCompatActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2343VerlagerungNaturalDoneActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2000CohomologicalPsiCnsActual
open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual
open LeanFormal.IUT.XiFPaper.S2027LocalArtinActual
open LeanFormal.IUT.XiFPaper.S2169MuQZConjugationActual
open LeanFormal.IUT.XiFPaper.S2200TransferNaturalityActual
open LeanFormal.IUT.XiFPaper.S2292TransferCompatActual
open LeanFormal.IUT.XiFPaper.S2300VerlagerungNaturalActual
open LeanFormal.IUT.XiFPaper.S2338TransferCompatDoneActual
open LeanFormal.IUT.XiFPaper.S2179StageConjEquivActual

universe u

theorem S2343_transferAb_natural_hom {G G' : Type u} [Group G] [Group G']
    (e : G ≃* G') (H : Subgroup G) [H.FiniteIndex]
    [(H.map e.toMonoidHom).FiniteIndex] :
    (Abelianization.map (Subgroup.equivMapOfInjective H e.toMonoidHom
        e.injective).toMonoidHom).comp (Verlagerung.transferAb H) =
      (Verlagerung.transferAb (H.map e.toMonoidHom)).comp
        (Abelianization.map e.toMonoidHom) := by
  apply Abelianization.hom_ext
  ext x
  simp only [MonoidHom.comp_apply, Abelianization.map_of]
  exact S2292_transferAb_natural e H default x

variable (p : Nat) [Fact (Nat.Prime p)]

abbrev S2343VerlagerungNaturalRequired : Prop :=
  S2300VerlagerungNaturalRequired (p := p)

abbrev S2343StageCompatibleRequired : Prop :=
  S2179TransferCompatible (p := p)

#check S2343_transferAb_natural_hom
#check S2343VerlagerungNaturalRequired
#print axioms S2343_transferAb_natural_hom

end LeanFormal.IUT.XiFPaper.S2343VerlagerungNaturalDoneActual

end