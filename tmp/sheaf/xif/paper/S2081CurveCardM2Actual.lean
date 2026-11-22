import tmp.sheaf.xif.paper.S2070CurveEtaleFundamentalCardActual
import tmp.sheaf.xif.paper.S2074CurveFiberFintypeActual
import tmp.sheaf.xif.paper.S2080CurveQuotientsTransportActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S2081CurveCardM2Actual
open LeanFormal.IUT
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.XiFPaper.S2070CurveEtaleFundamentalCardActual
open LeanFormal.IUT.XiFPaper.S2074CurveFiberFintypeActual
open LeanFormal.IUT.XiFPaper.S2080CurveQuotientsTransportActual
open LeanFormal.IUT.XiFPaper.S2073FiniteGroupQuotientActual
open CategoryTheory AlgebraicGeometry

universe u

/-- M2 discharged by S2074: geometric fibers of finite etale covers of the
curve are finite. -/
theorem s2081_geometricFiberFinite (K : Type u) [Field K]
    {Omega : Type u} [Field Omega]
    {x : Spec (CommRingCat.of Omega) ⟶ CurveBase K} :
    GeometricFiberFinite K Omega x := by
  intro Y
  exact S2074CurveFiberFintypeActual.geometricFiberObject_finite Y

/-- With M2 discharged, the corrected card is realized from exactly M1
(S2073 affine cocone) and M3 (fiber-functor certificate), plus the two
unconstrained card fields geometricPiOne/geometricConnectedness. -/
theorem s2081_cardV_of_M1_M3 (K : Type u) [Field K]
    {Omega : Type u} [Field Omega]
    {x : Spec (CommRingCat.of Omega) ⟶ CurveBase K}
    (hM1 : S2073AffineActionCoconeIsColimit (curveCoordinateRing K))
    (hcert : FiberFunctorCertificate
      (curveGeometricFiberFunctorFintype K (s2081_geometricFiberFinite K (Omega := Omega) (x := x))))
    (geomPi : ProfiniteGrp.{u + 1}) (geomConn : Prop) :
    Nonempty (CurveEtaleFundamentalGroupCardV K) :=
  curveEtaleFundamentalGroupCardV_realized_of_certificates K
    (s2080_curveQuotients_of_affine hM1)
    (s2081_geometricFiberFinite K (Omega := Omega) (x := x))
    hcert geomPi geomConn

end LeanFormal.IUT.XiFPaper.S2081CurveCardM2Actual
end