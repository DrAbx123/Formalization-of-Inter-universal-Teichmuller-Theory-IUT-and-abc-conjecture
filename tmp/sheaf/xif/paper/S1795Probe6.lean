import tmp.sheaf.xif.paper.S1641CoverMapCompositionActual

noncomputable section
set_option maxHeartbeats 8000000

namespace S1795P

open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT.XiFPaper.S1641CoverMapCompositionActual

universe u
variable {F : Type u} [Field F] {X : HyperbolicOrbicurve F}

theorem id_law (scheme : SchemeOverField F)
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
    Discrete.natTrans_app, id_eq, Category.comp_id]

theorem comp_law (scheme : SchemeOverField F)
    (point : Pseudofunctor.StrongTrans (schemeRepresentableEtalePseudofunctor F scheme) X.stack.fiber)
    {A B C : OrbicurveFiniteEtaleCover X}
    (f : OrbicurveFiniteEtaleCoverMap A B) (g : OrbicurveFiniteEtaleCoverMap B C) :
    (fun x => (OrbicurveFiniteEtaleCover.geometricFiberMap
        (S1641CoverMapComp f g).map (S1641CoverMapComp f g).commutes scheme point).obj x)
      = (fun x => (OrbicurveFiniteEtaleCover.geometricFiberMap
          g.map g.commutes scheme point).obj
            ((OrbicurveFiniteEtaleCover.geometricFiberMap
              f.map f.commutes scheme point).obj x)) := by
  funext x
  dsimp only [S1641CoverMapComp, OrbicurveFiniteEtaleCover.geometricFiberMap,
    CostructuredArrow.map₂, Comma.map]
  trace_state
  refine Comma.ext rfl rfl ?_
  apply heq_of_eq
  dsimp only
  trace_state
  simp?
  trace_state
  sorry

end S1795P
