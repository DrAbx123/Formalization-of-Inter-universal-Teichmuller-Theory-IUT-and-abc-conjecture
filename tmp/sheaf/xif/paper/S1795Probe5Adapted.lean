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
  trace_state
  simp? 
  trace_state
  sorry

end S1795P
