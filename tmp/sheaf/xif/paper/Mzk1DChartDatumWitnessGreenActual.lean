import tmp.sheaf.xif.paper.Mzk1GeomCoreChartDatumWitnessActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

/-! # D chart datum witness green consumer; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1DChartDatumWitnessGreenActual

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

universe u

variable {R : Type u} [CommRing R] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
  {F : Type*} [Field F] {P : Type*}

def dChartDatumWitnessGreen_restated (ord : P → F → ℤ) (X : FiniteMapChartData c ε)
    (hdeg : 0 < X.m)
    (B : FibreBridgeAbstract C Γ(C, X.U) F (X.U : Set C) X.f
      (C.basicOpen X.f : Set C) P ord)
    (Z : ZeroDivisorDatum P F ord) (hT : Z.T = B.Tplaces)
    (D : Set C) (hunram : UnramifiedOverZero c ε X.toFiniteMapData)
    (hpull : PullbackIsoDegree c ε X.toFiniteMapData D) :
    Mzk1GeometricCoreWitnessPreciseRestated c ε
      (B.placePoint '' (Z.T : Set P)) D :=
  chartDatum_restatedWitness ord X hdeg B Z hT D hunram hpull

def dChartDatumWitnessGreenRows : List (String × String × String) :=
  [ ("chart datum restated witness", "PROVED (conditional)", "dChartDatumWitnessGreen_restated") ]

theorem dChartDatumWitnessGreenRows_length : dChartDatumWitnessGreenRows.length = 1 := rfl

#check dChartDatumWitnessGreen_restated
#check dChartDatumWitnessGreenRows_length

end LeanFormal.IUT.XiFPaper.Mzk1DChartDatumWitnessGreenActual
end