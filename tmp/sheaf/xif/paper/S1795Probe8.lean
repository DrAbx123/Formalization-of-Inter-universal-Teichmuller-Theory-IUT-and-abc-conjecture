import tmp.sheaf.xif.paper.S1641CoverMapCompositionActual

noncomputable section
set_option maxHeartbeats 8000000

namespace S1795R

open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT.XiFPaper.S1641CoverMapCompositionActual

universe u
variable {F : Type u} [Field F] {X : HyperbolicOrbicurve F}
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

set_option backward.isDefEq.respectTransparency false in
theorem id_resp (scheme : SchemeOverField F)
    (point : Pseudofunctor.StrongTrans (schemeRepresentableEtalePseudofunctor F scheme) X.stack.fiber)
    (cover : OrbicurveFiniteEtaleCover X) :
    (fun x => (OrbicurveFiniteEtaleCover.geometricFiberMap
        (S1641CoverMapId cover).map (S1641CoverMapId cover).commutes scheme point).obj x)
      = id := by
  funext x
  dsimp only [S1641CoverMapId, OrbicurveFiniteEtaleCover.geometricFiberMap,
    CostructuredArrow.map₂, Comma.map]
  refine Comma.ext rfl rfl ?_
  apply heq_of_eq
  dsimp only
  simp only [Functor.id_obj, Pseudofunctor.StrongTrans.comp_app, eqToHom_refl,
    Pseudofunctor.StrongTrans.isoMk_hom_as_app, Category.id_comp, Cat.leftUnitor_hom_toNatTrans,
    NatTrans.comp_app, Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app, Functor.id_map,
    Discrete.natTrans_app, id_eq]
  simp only [Category.id_comp, Category.comp_id]

set_option backward.defeqAttrib.useBackward true in
theorem id_deff (scheme : SchemeOverField F)
    (point : Pseudofunctor.StrongTrans (schemeRepresentableEtalePseudofunctor F scheme) X.stack.fiber)
    (cover : OrbicurveFiniteEtaleCover X) :
    (fun x => (OrbicurveFiniteEtaleCover.geometricFiberMap
        (S1641CoverMapId cover).map (S1641CoverMapId cover).commutes scheme point).obj x)
      = id := by
  funext x
  dsimp only [S1641CoverMapId, OrbicurveFiniteEtaleCover.geometricFiberMap,
    CostructuredArrow.map₂, Comma.map]
  refine Comma.ext rfl rfl ?_
  apply heq_of_eq
  dsimp only
  simp only [Functor.id_obj, Pseudofunctor.StrongTrans.comp_app, eqToHom_refl,
    Pseudofunctor.StrongTrans.isoMk_hom_as_app, Category.id_comp, Cat.leftUnitor_hom_toNatTrans,
    NatTrans.comp_app, Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app, Functor.id_map,
    Discrete.natTrans_app, id_eq]
  simp only [Category.id_comp, Category.comp_id]

theorem id_erw (scheme : SchemeOverField F)
    (point : Pseudofunctor.StrongTrans (schemeRepresentableEtalePseudofunctor F scheme) X.stack.fiber)
    (cover : OrbicurveFiniteEtaleCover X) :
    (fun x => (OrbicurveFiniteEtaleCover.geometricFiberMap
        (S1641CoverMapId cover).map (S1641CoverMapId cover).commutes scheme point).obj x)
      = id := by
  funext x
  dsimp only [S1641CoverMapId, OrbicurveFiniteEtaleCover.geometricFiberMap,
    CostructuredArrow.map₂, Comma.map]
  refine Comma.ext rfl rfl ?_
  apply heq_of_eq
  dsimp only
  simp only [Functor.id_obj, Pseudofunctor.StrongTrans.comp_app, eqToHom_refl,
    Pseudofunctor.StrongTrans.isoMk_hom_as_app, Category.id_comp, Cat.leftUnitor_hom_toNatTrans,
    NatTrans.comp_app, Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app, Functor.id_map,
    Discrete.natTrans_app, id_eq]
    erw [Category.id_comp]
  erw [Category.id_comp]
  erw [Category.comp_id]

end S1795R
