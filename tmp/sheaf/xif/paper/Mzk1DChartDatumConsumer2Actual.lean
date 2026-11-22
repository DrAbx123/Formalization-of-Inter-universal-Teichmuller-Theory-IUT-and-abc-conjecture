import tmp.sheaf.xif.paper.Mzk1DChartDatumWitnessGreenActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

/-! # D chart datum consumer 2; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1DChartDatumConsumer2Actual

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
open LeanFormal.IUT.XiFPaper.Mzk1DChartDatumWitnessGreenActual

universe u

variable {R : Type u} [CommRing R] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
  {F : Type*} [Field F] {P : Type*}

def dChartDatumConsumer2_witness (ord : P → F → ℤ) (X : FiniteMapChartData c ε)
    (hdeg : 0 < X.m)
    (B : FibreBridgeAbstract C Γ(C, X.U) F (X.U : Set C) X.f
      (C.basicOpen X.f : Set C) P ord)
    (Z : ZeroDivisorDatum P F ord) (hT : Z.T = B.Tplaces)
    (D : Set C) (hunram : UnramifiedOverZero c ε X.toFiniteMapData)
    (hpull : PullbackIsoDegree c ε X.toFiniteMapData D) :
    Mzk1GeometricCoreWitnessPreciseRestated c ε
      (B.placePoint '' (Z.T : Set P)) D :=
  dChartDatumWitnessGreen_restated ord X hdeg B Z hT D hunram hpull

def dChartDatumConsumer2Rows : List (String × String × String) :=
  [ ("witness", "PROVED (conditional)", "dChartDatumConsumer2_witness") ]

theorem dChartDatumConsumer2Rows_length : dChartDatumConsumer2Rows.length = 1 := rfl

#check dChartDatumConsumer2Rows_length

end LeanFormal.IUT.XiFPaper.Mzk1DChartDatumConsumer2Actual
end