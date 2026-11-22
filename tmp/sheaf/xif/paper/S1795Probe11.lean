import tmp.sheaf.xif.paper.S1641CoverMapCompositionActual

noncomputable section
set_option maxHeartbeats 8000000

namespace S1795U

open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT.XiFPaper.S1641CoverMapCompositionActual

universe u
variable {F : Type u} [Field F] {X : HyperbolicOrbicurve F}
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

set_option backward.isDefEq.respectTransparency false in
theorem comp_v1 (scheme : SchemeOverField F)
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
  refine Comma.ext rfl rfl ?_
  apply heq_of_eq
  dsimp only
  rw [S1641CoverMapComp_commutes_hom_app]
  simp
  trace_state
  sorry

set_option backward.isDefEq.respectTransparency false in
theorem comp_v2 (scheme : SchemeOverField F)
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
  refine Comma.ext rfl rfl ?_
  apply heq_of_eq
  dsimp only
  rw [S1641CoverMapComp_commutes_hom_app]
  simp only [Pseudofunctor.StrongTrans.associator, Cat.Hom.toNatTrans_comp, NatTrans.comp_app,
    Cat.whiskerLeft_toNatTrans, Functor.whiskerLeft_app, Cat.associator_hom_toNatTrans,
    Functor.associator_hom_app, Pseudofunctor.StrongTrans.comp_app, eqToHom_refl,
    Category.id_comp, Functor.rightUnitor_inv_app, Functor.id_map, Discrete.natTrans_app, id_eq,
    Category.assoc]
  trace_state
  sorry

end S1795U
