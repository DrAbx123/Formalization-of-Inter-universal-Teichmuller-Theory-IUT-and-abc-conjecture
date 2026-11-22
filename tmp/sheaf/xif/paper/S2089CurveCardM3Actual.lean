import tmp.sheaf.xif.paper.S2087AffineQuotientPackagingActual
import tmp.sheaf.xif.paper.S2081CurveCardM2Actual
import tmp.sheaf.xif.paper.S2088FiberFunctorCertificateActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S2089CurveCardM3Actual
open LeanFormal.IUT
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.XiFPaper.S2070CurveEtaleFundamentalCardActual
open LeanFormal.IUT.XiFPaper.S2087AffineQuotientPackagingActual
open LeanFormal.IUT.XiFPaper.S2081CurveCardM2Actual
open LeanFormal.IUT.XiFPaper.S2088FiberFunctorCertificateActual
open CategoryTheory AlgebraicGeometry

universe u

/-- CardV with M1 and M2 unconditionally closed; only the five type-level
fiber-functor fields (M3) plus the two unconstrained card fields remain. -/
theorem s2089_cardV_of_remaining (K : Type u) [Field K]
    {Omega : Type u} [Field Omega]
    {x : Spec (CommRingCat.of Omega) ⟶ CurveBase K}
    (h : RemainingTypeLevel K Omega x)
    (geomPi : ProfiniteGrp.{u + 1}) (geomConn : Prop) :
    Nonempty (CurveEtaleFundamentalGroupCardV K) :=
  curveEtaleFundamentalGroupCardV_realized_of_remaining
    (s2073AffineActionCoconeIsColimit (curveCoordinateRing K))
    (s2081_geometricFiberFinite K (Omega := Omega) (x := x))
    h geomPi geomConn

end LeanFormal.IUT.XiFPaper.S2089CurveCardM3Actual
end