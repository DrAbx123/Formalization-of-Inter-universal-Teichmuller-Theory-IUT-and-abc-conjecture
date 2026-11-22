import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Equivalence
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Preserves.Finite

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
open CategoryTheory CategoryTheory.Limits

universe u v

namespace S1753Probe

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
variable (E : C ≌ D) [GaloisCategory D]

lemma unit_triangle (X : C) :
    E.functor.map (E.unitIso.inv.app X) =
      E.counitIso.hom.app (E.functor.obj X) := by
  have h := E.counitIso_functor_comp X
  have h2 : E.functor.map (E.unitIso.inv.app X) =
      inv (E.counitIso.inv.app (E.functor.obj X)) :=
    IsIso.eq_inv_of_hom_inv_id h
  simpa using h2

lemma key (Z : D) (Y : C) (u : Z ⟶ E.functor.obj Y) :
    E.functor.map (E.inverse.map u ≫ E.unitIso.inv.app Y) =
      E.counitIso.hom.app Z ≫ u := by
  rw [Functor.map_comp]
  rw [show E.functor.map (E.unitIso.inv.app Y) =
      E.counitIso.hom.app (E.functor.obj Y) from unit_triangle E Y]
  simpa only [Functor.id_map, Functor.comp_map] using E.counitIso.hom.naturality u

set_option maxHeartbeats 1000000 in
noncomputable def pre : PreGaloisCategory C where
  hasTerminal := (Equivalence.hasTerminal_iff E).2 inferInstance
  hasPullbacks := Adjunction.hasLimitsOfShape_of_equivalence (J := WalkingCospan) E.functor
  hasFiniteCoproducts :=
    ⟨fun n => Adjunction.hasColimitsOfShape_of_equivalence (J := Discrete (Fin n)) E.functor⟩
  hasQuotientsByFiniteGroups :=
    fun G _ _ => Adjunction.hasColimitsOfShape_of_equivalence (J := SingleObj G) E.functor
  monoInducesIsoOnDirectSummand := by
    intro X Y i _
    haveI : Mono (E.functor.map i) := inferInstance
    obtain ⟨Z, u, ⟨hc⟩⟩ :=
      PreGaloisCategory.monoInducesIsoOnDirectSummand (C := D) (E.functor.map i)
    let u' : E.inverse.obj Z ⟶ Y := E.inverse.map u ≫ E.unitIso.inv.app Y
    refine ⟨E.inverse.obj Z, u', ⟨?_⟩⟩
    let cC : BinaryCofan X (E.inverse.obj Z) := BinaryCofan.mk i u'
    apply isColimitOfReflects E.functor
    let cMap : Cocone (pair X (E.inverse.obj Z) ⋙ E.functor) := E.functor.mapCocone cC
    let gammaIso : (pair X (E.inverse.obj Z) ⋙ E.functor) ≅
        pair (E.functor.obj X) Z :=
      mapPairIso (Iso.refl (E.functor.obj X)) (E.counitIso.app Z)
    let cD'' : Cocone (pair X (E.inverse.obj Z) ⋙ E.functor) :=
      (Cocone.precompose gammaIso.hom).obj (BinaryCofan.mk (E.functor.map i) u)
    have hcD'' : IsColimit cD'' :=
      (IsColimit.precomposeHomEquiv gammaIso (BinaryCofan.mk (E.functor.map i) u)).symm hc
    have hright : E.functor.map u' = E.counitIso.hom.app Z ≫ u := key E Z Y u
    refine hcD''.ofIsoColimit (Cocone.ext (Iso.refl _) ?_)
    intro j
    rcases j with ⟨⟨⟩⟩
    · simp only [cD'', cMap, cC, gammaIso, Iso.refl_hom, Category.comp_id,
        Functor.mapCocone_ι_app, Cocone.precompose_obj_ι, NatTrans.comp_app,
        mapPairIso_hom_app, BinaryCofan.mk]
      exact Category.id_comp _
    · simp only [cD'', cMap, cC, gammaIso, Iso.refl_hom, Category.comp_id,
        Functor.mapCocone_ι_app, Cocone.precompose_obj_ι, NatTrans.comp_app,
        mapPairIso_hom_app, Category.id_comp, BinaryCofan.mk, hright]
      rfl

end S1753Probe
