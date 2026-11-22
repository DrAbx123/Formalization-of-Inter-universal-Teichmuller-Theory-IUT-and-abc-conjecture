import tmp.sheaf.xif.paper.S2072HasQuotientsActual
import tmp.sheaf.xif.paper.S2081CurveCardM2Actual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S2082CurveM1PackagingActual

universe u
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.XiFPaper.S2070CurveEtaleFundamentalCardActual
open LeanFormal.IUT.XiFPaper.S2072HasQuotientsActual
open LeanFormal.IUT.XiFPaper.S2081CurveCardM2Actual
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

/-- The S2072 packaging residual is exactly the S2073 affine cocone target. -/
noncomputable def s2082_affineCoconeTarget_of_packaging (K : Type u) [Field K]
    (h : AffineQuotientColimitPackaging (curveCoordinateRing K)) :
    LeanFormal.IUT.XiFPaper.S2073FiniteGroupQuotientActual.S2073AffineActionCoconeIsColimit
      (curveCoordinateRing K) where
  isColimit := by
    intro G _ _ F
    have h' := h G F
    simpa [affineActionCocone] using h'

/-- M1 from packaging, hence CardV from packaging plus M3, with M2 discharged. -/
theorem s2082_cardV_of_packaging_M3 (K : Type u) [Field K]
    {Omega : Type u} [Field Omega]
    {x : Spec (CommRingCat.of Omega) ⟶ CurveBase K}
    (hM1 : AffineQuotientColimitPackaging (curveCoordinateRing K))
    (hcert : FiberFunctorCertificate
      (curveGeometricFiberFunctorFintype K (s2081_geometricFiberFinite K (Omega := Omega) (x := x))))
    (geomPi : ProfiniteGrp.{u + 1}) (geomConn : Prop) :
    Nonempty (CurveEtaleFundamentalGroupCardV K) :=
  s2081_cardV_of_M1_M3 K
    (s2082_affineCoconeTarget_of_packaging K hM1)
    hcert geomPi geomConn

end LeanFormal.IUT.XiFPaper.S2082CurveM1PackagingActual
end