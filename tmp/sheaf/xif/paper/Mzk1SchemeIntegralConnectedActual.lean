/- Generic: an integral scheme is connected (route 2.4 L144 的「因而几何连通」落点辅助件).
   Four-part reuse: Mathlib-only; IsIntegral = IrreducibleSpace + IsReduced; irreducible implies
   preconnected, Nonempty from IsIntegral.nonempty. No old-corpus conclusions. ADAPTER. -/
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Topology.Connected.Basic
import Mathlib.Tactic

noncomputable section
open AlgebraicGeometry CategoryTheory
namespace LeanFormal.IUT.XiFPaper.Mzk1SchemeIntegralConnectedActual

/-- 整概型是连通空间。 -/
theorem connectedSpace_of_isIntegral {X : Scheme} [IsIntegral X] : ConnectedSpace X := by
  haveI : Nonempty X := IsIntegral.nonempty
  infer_instance

/-- 整概型给出 PreconnectedSpace（备用）。 -/
theorem preconnectedSpace_of_isIntegral {X : Scheme} [IsIntegral X] : PreconnectedSpace X :=
  inferInstance

#print axioms connectedSpace_of_isIntegral
#print axioms preconnectedSpace_of_isIntegral

end LeanFormal.IUT.XiFPaper.Mzk1SchemeIntegralConnectedActual
