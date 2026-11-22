import tmp.sheaf.xif.paper.S2348CastByCasesActual
import tmp.sheaf.xif.paper.S2343VerlagerungNaturalDoneActual
import tmp.sheaf.xif.paper.S2336TransferCompActual
import tmp.sheaf.xif.paper.S2338TransferCompatDoneActual
import tmp.sheaf.xif.paper.S2341AbMapInclusionActual
import tmp.sheaf.xif.paper.S2179StageConjEquivActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2371HnatExplicitActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual
open LeanFormal.IUT.XiFPaper.S2343VerlagerungNaturalDoneActual
open LeanFormal.IUT.XiFPaper.S2348CastByCasesActual
open LeanFormal.IUT.XiFPaper.S2000CohomologicalPsiCnsActual
open LeanFormal.IUT.XiFPaper.S2027LocalArtinActual
open LeanFormal.IUT.XiFPaper.S2169MuQZConjugationActual
open LeanFormal.IUT.XiFPaper.S2200TransferNaturalityActual
open LeanFormal.IUT.XiFPaper.S2300VerlagerungNaturalActual
open LeanFormal.IUT.XiFPaper.S2317SubgroupOfApplyActual
open LeanFormal.IUT.XiFPaper.S2336TransferCompActual
open LeanFormal.IUT.XiFPaper.S2338TransferCompatDoneActual
open LeanFormal.IUT.XiFPaper.S2341AbMapInclusionActual
open LeanFormal.IUT.XiFPaper.S2179StageConjEquivActual

universe u

theorem S2371_hnat {G G' : Type u} [Group G] [Group G']
    (eK : G ≃* G') (H : Subgroup G) (H' : Subgroup G')
    [H.FiniteIndex] [(H.map eK.toMonoidHom).FiniteIndex] [H'.FiniteIndex]
    (hcast : H.map eK.toMonoidHom = H') :
    (Abelianization.map ((Subgroup.equivMapOfInjective H eK.toMonoidHom
        eK.injective).trans (MulEquiv.subgroupCongr hcast)).toMonoidHom).comp
        (Verlagerung.transferAb H) =
      (Verlagerung.transferAb H').comp
        (Abelianization.map eK.toMonoidHom) := by
  let e0 := Subgroup.equivMapOfInjective H eK.toMonoidHom eK.injective
  let eHsub := e0.trans (MulEquiv.subgroupCongr hcast)
  have h0 : (Abelianization.map e0.toMonoidHom).comp
      (Verlagerung.transferAb H) =
    (Verlagerung.transferAb (H.map eK.toMonoidHom)).comp
      (Abelianization.map eK.toMonoidHom) :=
    S2343_transferAb_natural_hom (e := eK) H
  have hc : (Abelianization.map (MulEquiv.subgroupCongr hcast).toMonoidHom).comp
      (Verlagerung.transferAb (H.map eK.toMonoidHom)) =
    Verlagerung.transferAb H' :=
    S2348_transferAb_subgroupCongr hcast
  have hmap : (Abelianization.map eHsub.toMonoidHom) =
      (Abelianization.map (MulEquiv.subgroupCongr hcast).toMonoidHom).comp
        (Abelianization.map e0.toMonoidHom) := by
    have hcomp : eHsub.toMonoidHom =
        (MulEquiv.subgroupCongr hcast).toMonoidHom.comp e0.toMonoidHom := by
      ext x
      rfl
    rw [hcomp, Abelianization.map_comp]
  rw [hmap]
  rw [MonoidHom.comp_assoc]
  rw [h0]
  rw [← MonoidHom.comp_assoc]
  rw [hc]


variable (p : Nat) [Fact (Nat.Prime p)]

theorem S2371_verlagerung_natural : S2300VerlagerungNaturalRequired (p := p) := by
  intro g H K h
  let H' := S2169ConjIndex p g H
  let K' := S2169ConjIndex p g K
  let h' : H' ≤ K' := S2338_conjIndex_mono p g h
  refine ⟨h', ?_⟩
  haveI : Subgroup.FiniteIndex H.toSubgroup := openSubgroup_finiteIndex p H
  haveI : Subgroup.FiniteIndex K.toSubgroup := openSubgroup_finiteIndex p K
  haveI : Subgroup.FiniteIndex H'.toSubgroup := openSubgroup_finiteIndex p H'
  haveI : Subgroup.FiniteIndex K'.toSubgroup := openSubgroup_finiteIndex p K'
  let Hsub := H.toSubgroup.subgroupOf K.toSubgroup
  let hcast := S2317_subgroupOf_map p g H K h
  let eH := (S2200ConjEquiv p g H).toMonoidHom
  let eK := (S2200ConjEquiv p g K).toMonoidHom
  rw [S2336_verlagerungOpen_eq p H K h, S2336_verlagerungOpen_eq p H' K' h']
  rw [← MonoidHom.comp_assoc]
  rw [S2341_abmap_inclusion p g H K h]
  rw [MonoidHom.comp_assoc]
  haveI : Hsub.FiniteIndex := inferInstance
  haveI : (Hsub.map (S2200ConjEquiv p g K).toMonoidHom).FiniteIndex :=
    hcast ▸ (inferInstance : (H'.toSubgroup.subgroupOf K'.toSubgroup).FiniteIndex)
  haveI : (H'.toSubgroup.subgroupOf K'.toSubgroup).FiniteIndex := inferInstance
  have hnat := S2371_hnat (eK := S2200ConjEquiv p g K) Hsub
    (H'.toSubgroup.subgroupOf K'.toSubgroup) hcast
  dsimp [Hsub] at hnat ⊢
  rw [hnat]
  rw [MonoidHom.comp_assoc]

#check S2371_verlagerung_natural
#print axioms S2371_verlagerung_natural

#check S2371_hnat
#print axioms S2371_hnat

end LeanFormal.IUT.XiFPaper.S2371HnatExplicitActual

end