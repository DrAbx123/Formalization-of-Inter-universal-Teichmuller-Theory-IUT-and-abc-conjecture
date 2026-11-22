import tmp.sheaf.xif.paper.S2106CurveM3Actual
noncomputable section
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open LeanFormal.IUT.XiFPaper.S2106CurveM3Actual
open LeanFormal.IUT.XiFPaper.S2070CurveEtaleFundamentalCardActual
open LeanFormal.IUT.XiFPaper.S2088FiberFunctorCertificateActual
universe u
#check @preservesPullbacks_typeLevel
#check @preservesFiniteCoproducts_typeLevel
#check @certificate_preservesPullbacks_m3
#check @certificate_preservesFiniteCoproducts_m3
#check @RemainingTypeLevelThree
#check @certificate_of_remaining_three
#check @s2106_cardV_of_remaining_three
#check @PreservesEpisCounterexample
#check @not_preservesEpis_of_counterexample
#check @ReflectsIsosCounterexample
#check @not_reflectsIsos_of_counterexample
example {K : Type u} [Field K] {Omega : Type u} [Field Omega]
    {x : Spec (CommRingCat.of Omega) ⟶ CurveBase K} :
    PreservesLimitsOfShape WalkingCospan (curveGeometricFiberFunctor K Omega x) :=
  preservesPullbacks_typeLevel
example {K : Type u} [Field K] {Omega : Type u} [Field Omega]
    {x : Spec (CommRingCat.of Omega) ⟶ CurveBase K} :
    PreservesFiniteCoproducts (curveGeometricFiberFunctor K Omega x) :=
  preservesFiniteCoproducts_typeLevel x
end
