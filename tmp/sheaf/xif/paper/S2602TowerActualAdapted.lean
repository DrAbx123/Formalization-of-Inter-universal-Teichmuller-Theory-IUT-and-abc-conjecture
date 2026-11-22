import tmp.sheaf.xif.paper.S2600TIntegralClosureActual
import tmp.sheaf.xif.paper.S2536LocalizedPowersActual

noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace LeanFormal.IUT.XiFPaper.S2602TowerActualAdapted

open LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
open LeanFormal.IUT.XiFPaper.S2599TInstancesActual
open LeanFormal.IUT.XiFPaper.S2600TIntegralClosureActual

local instance : Algebra C T := gCT.toAlgebra

lemma hcomp : (algebraMap S T).comp (algebraMap C S) = gCT := by
  ext x
  change liftST (algebraMap C S x) = gCT x
  exact IsLocalization.lift_comp (M := Algebra.algebraMapSubmonoid C (Submonoid.powers (c : ℤ)))
    (g := gCT) (fun y => gCT_unit y.1 y.2) ▸ rfl

lemma isScalarTower_CST : IsScalarTower C S T := by
  refine IsScalarTower.mk ?_
  intro c s t
  simp [hcomp]

end LeanFormal.IUT.XiFPaper.S2602TowerActualAdapted
end