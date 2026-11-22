/- G1-A route 2.4 L144 (h) landing: Y_n (x) kbar is connected (geometrically connected).
   Reuse: kbar_integral (S4, 21:38:34Z) + connectedSpace_of_isIntegral (21:23:28Z). ADAPTER. -/
import tmp.sheaf.xif.paper.Mzk1G1FermatKbarIntegralActual
import tmp.sheaf.xif.paper.Mzk1SchemeIntegralConnectedActual
import Mathlib.Tactic

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatKbarConnectedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatKbarSpecActual

/-- **几何连通落点**：Y_n (x) kbar 连通（route 2.4 L144「因而几何连通」）。 -/
theorem kbar_connected (n : Nat) (hn : 0 < n) :
    ConnectedSpace (pullback (Mzk1G1FermatCurveToSpecActual.fermatCurveToSpec n) gK : Scheme) := by
  haveI := Mzk1G1FermatKbarIntegralActual.kbar_integral n hn
  exact Mzk1SchemeIntegralConnectedActual.connectedSpace_of_isIntegral

/-- 连通的 Nonempty 形式（便于下游消费）。 -/
theorem kbar_nonempty (n : Nat) (hn : 0 < n) :
    Nonempty (pullback (Mzk1G1FermatCurveToSpecActual.fermatCurveToSpec n) gK : Scheme) := by
  haveI := Mzk1G1FermatKbarIntegralActual.kbar_integral n hn
  exact IsIntegral.nonempty

#print axioms kbar_connected
#print axioms kbar_nonempty

end LeanFormal.IUT.XiFPaper.Mzk1G1FermatKbarConnectedActual