import tmp.sheaf.xif.paper.S2088FiberFunctorCertificateActual

noncomputable section
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open LeanFormal.IUT.XiFPaper.S2088FiberFunctorCertificateActual
open LeanFormal.IUT.XiFPaper.S2070CurveEtaleFundamentalCardActual
universe u

section
variable {K : Type u} [Field K] {Omega : Type u} [Field Omega]
  {x : Spec (CommRingCat.of Omega) ⟶ CurveBase K}

-- The exact field type of the S2070 certificate, item 1:
example (hfin : GeometricFiberFinite K Omega x)
    (h : FiberFunctorCertificate (curveGeometricFiberFunctorFintype K hfin)) :
    PreservesLimitsOfShape (Discrete PEmpty.{1})
      (curveGeometricFiberFunctorFintype K hfin) :=
  h.preservesTerminalObjects

-- ... and it is inhabited unconditionally (no sorry, no extra hypothesis beyond the
-- finiteness of the geometric fiber, which S2074/S2081 discharge unconditionally).
example (hfin : GeometricFiberFinite K Omega x) :
    PreservesLimitsOfShape (Discrete PEmpty.{1})
      (curveGeometricFiberFunctorFintype K hfin) :=
  certificate_preservesTerminalObjects hfin

-- The exact field type of item 2, and its transport:
example (hfin : GeometricFiberFinite K Omega x)
    (h : FiberFunctorCertificate (curveGeometricFiberFunctorFintype K hfin)) :
    PreservesLimitsOfShape WalkingCospan (curveGeometricFiberFunctorFintype K hfin) :=
  h.preservesPullbacks

example (hfin : GeometricFiberFinite K Omega x)
    (h : PreservesLimitsOfShape WalkingCospan (curveGeometricFiberFunctor K Omega x)) :
    PreservesLimitsOfShape WalkingCospan (curveGeometricFiberFunctorFintype K hfin) :=
  certificate_preservesPullbacks hfin h

-- The full certificate from the remaining type-level statements.
example (hfin : GeometricFiberFinite K Omega x) (h : RemainingTypeLevel K Omega x) :
    FiberFunctorCertificate (curveGeometricFiberFunctorFintype K hfin) :=
  certificate_of_remaining hfin h

end
end
