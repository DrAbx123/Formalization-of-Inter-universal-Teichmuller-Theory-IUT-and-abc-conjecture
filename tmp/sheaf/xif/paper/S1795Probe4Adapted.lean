import tmp.sheaf.xif.paper.S1764ActualFiberFunctorActual

noncomputable section
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S1795Probe4Adapted

open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT.XiFPaper.S1764ActualFiberFunctorActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1641CoverMapCompositionActual

theorem test_id (cover : OrbicurveFiniteEtaleCover S1764Orbicurve) :
    S1764RawFiberMap (S1641CoverMapId cover : OrbicurveFiniteEtaleCoverMap cover cover) = id := by
  funext x
  dsimp only [S1764RawFiberMap, S1764RawFiberFunctor, S1641CoverMapId,
    OrbicurveFiniteEtaleCover.geometricFiberMap, CostructuredArrow.map₂, Comma.map]
  refine Comma.ext rfl rfl ?_
  apply heq_of_eq
  dsimp only
  trace_state
  simp?
  trace_state
  sorry

end LeanFormal.IUT.XiFPaper.S1795Probe4Adapted
