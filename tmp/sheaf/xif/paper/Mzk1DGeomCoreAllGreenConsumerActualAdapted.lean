import tmp.sheaf.xif.paper.Mzk1DChartDatumWitnessGreenActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

/-! # D GeomCore all-green consumer; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1DGeomCoreAllGreenConsumerActualAdapted

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

theorem dGeomCoreAllGreenConsumer_fibre (ord : P → F → ℤ) (X : FiniteMapChartData c ε)
    (B : FibreBridgeAbstract C Γ(C, X.U) F (X.U : Set C) X.f
      (C.basicOpen X.f : Set C) P ord)
    (Z : ZeroDivisorDatum P F ord) (hT : Z.T = B.Tplaces) :
    FibreOverZeroEq c ε X.toFiniteMapData (B.placePoint '' (Z.T : Set P)) :=
  chartDatum_fibre ord X B Z hT

def dGeomCoreAllGreenConsumerRows : List (String × String × String) :=
  [ ("chart datum fibre", "PROVED", "dGeomCoreAllGreenConsumer_fibre") ]

theorem dGeomCoreAllGreenConsumerRows_length : dGeomCoreAllGreenConsumerRows.length = 1 := rfl

#check dGeomCoreAllGreenConsumer_fibre
#check dGeomCoreAllGreenConsumerRows_length

end LeanFormal.IUT.XiFPaper.Mzk1DGeomCoreAllGreenConsumerActualAdapted
end