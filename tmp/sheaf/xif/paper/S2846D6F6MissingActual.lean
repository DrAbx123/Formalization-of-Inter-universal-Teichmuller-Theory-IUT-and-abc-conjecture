import tmp.sheaf.xif.paper.S2844D6F6BaseChangeActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36OrbicurveFeasibility

noncomputable section
open WeierstrassCurve LeanFormal.IUT CategoryTheory AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.S2844D6F6BaseChangeActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.OrbicurveFeasibility
open LeanFormal.IUT.XiFPaper.S2801E37ProjectiveClosure
open LeanFormal.IUT.XiFPaper.S2801D6FaithfulActual
open LeanFormal.IUT.XiFPaper.S2813E37TwoFPointsActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2846D6F6MissingActual

local instance : Field K := inferInstance
local instance : DecidableEq K := Classical.decEq _

theorem S2846_curvePointRealization (h0 : S2844ZeroPreimage) :
    ∃ f : S2844Fiber.obj (LocallyDiscrete.mk (Opposite.op (baseSchemeObject K))) →
        S2844Punctured.curve.toProjective.Point, Function.Surjective f := by
  classical
  let cp := S2844CurvePointRealization h0
  refine ⟨fun z => cp.pointMap (Discrete.as z), ?_⟩
  intro P
  obtain ⟨x, hx⟩ := cp.surjective P
  exact ⟨Discrete.mk x, by simp [cp, hx]⟩

noncomputable def S2846D6 (h0 : S2844ZeroPreimage)
    (hndg : ¬ IsPointFiber S2844Fiber) :
    MissingD6GeometricRealization K where
  curve := S2844Punctured
  fiber := S2844Fiber
  isStack := S2844Fiber_isStack
  nondegenerate := hndg
  curvePointRealization := S2846_curvePointRealization h0

end LeanFormal.IUT.XiFPaper.S2846D6F6MissingActual
end
