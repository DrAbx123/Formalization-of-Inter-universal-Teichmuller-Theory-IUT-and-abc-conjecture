import tmp.sheaf.xif.paper.S1764ActualFiberFunctorActual

noncomputable section
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S1795Probe2Adapted

open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT.XiFPaper.S1764ActualFiberFunctorActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1641CoverMapCompositionActual

set_option pp.universes false

theorem test_id (cover : OrbicurveFiniteEtaleCover S1764Orbicurve) :
    S1764RawFiberMap (S1641CoverMapId cover : OrbicurveFiniteEtaleCoverMap cover cover) = id := by
  funext x
  obtain ⟨Y, r, s⟩ := x
  cases r
  show (OrbicurveFiniteEtaleCover.geometricFiberMap (S1641CoverMapId cover).map
      (S1641CoverMapId cover).commutes S1764BaseScheme S1764BasePoint).obj
        (Comma.mk Y PUnit.unit s) = Comma.mk Y PUnit.unit s
  dsimp only [OrbicurveFiniteEtaleCover.geometricFiberMap, CostructuredArrow.map₂, Comma.map,
    S1641CoverMapId]
  trace_state
  sorry

end LeanFormal.IUT.XiFPaper.S1795Probe2Adapted
