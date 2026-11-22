import tmp.sheaf.xif.paper.Mzk1GeomCoreChartDatumWitnessActual
import tmp.sheaf.xif.paper.Mzk1GeomCoreChartBasicFactsActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

/-! # D GeomCore all-green bundle (def + theorem split); no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1DGeomCoreAllGreenActual

open CategoryTheory AlgebraicGeometry
open NeronModelInfra
open LeanFormal.IUT.XiFPaper.Mzk1GeometricCoreRealStructureActual
open LeanFormal.IUT.XiFPaper.Mzk1GeometricCorePreciseActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreFoundationActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreFoundationActual.SchemeLayer
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreBridgeInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreChartWitnessActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreChartDatumWitnessActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreFiniteMapChartInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreChartBasicFactsActual

universe u

variable {R : Type u} [CommRing R] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
  {F : Type*} [Field F] {P : Type*}

def dGeomCoreAllGreen_witness (ord : P → F → ℤ) (X : FiniteMapChartData c ε)
    (hdeg : 0 < X.m)
    (B : FibreBridgeAbstract C Γ(C, X.U) F (X.U : Set C) X.f
      (C.basicOpen X.f : Set C) P ord)
    (Z : ZeroDivisorDatum P F ord) (hT : Z.T = B.Tplaces)
    (D : Set C) (hunram : UnramifiedOverZero c ε X.toFiniteMapData)
    (hpull : PullbackIsoDegree c ε X.toFiniteMapData D) :
    Mzk1GeometricCoreWitnessPreciseRestated c ε
      (B.placePoint '' (Z.T : Set P)) D :=
  chartDatum_restatedWitness ord X hdeg B Z hT D hunram hpull

theorem dGeomCoreAllGreen_chart (X : FiniteMapChartData c ε) :
    X.toFiniteMapData.m = X.m := chartBasic_m X

def dGeomCoreAllGreenRows : List (String × String × String) :=
  [ ("restated witness", "PROVED (conditional)", "dGeomCoreAllGreen_witness"),
    ("chart degree identity", "PROVED", "dGeomCoreAllGreen_chart") ]

theorem dGeomCoreAllGreenRows_length : dGeomCoreAllGreenRows.length = 2 := rfl

#check dGeomCoreAllGreen_chart
#check dGeomCoreAllGreenRows_length

end LeanFormal.IUT.XiFPaper.Mzk1DGeomCoreAllGreenActual
end