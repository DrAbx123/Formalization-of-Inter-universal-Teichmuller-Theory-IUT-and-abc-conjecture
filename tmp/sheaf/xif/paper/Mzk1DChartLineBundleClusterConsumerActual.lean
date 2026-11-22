import tmp.sheaf.xif.paper.Mzk1DChartLineBundleRollupActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

/-! # D chart/line-bundle cluster consumer; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1DChartLineBundleClusterConsumerActual

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
open LeanFormal.IUT.XiFPaper.Mzk1DChartLineBundleRollupActual

universe u

variable {R : Type u} [CommRing R] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
  {F : Type*} [Field F] {P : Type*}

theorem dChartLineBundleClusterConsumer_fibre (ord : P → F → ℤ) (X : FiniteMapChartData c ε)
    (B : FibreBridgeAbstract C Γ(C, X.U) F (X.U : Set C) X.f
      (C.basicOpen X.f : Set C) P ord)
    (Z : ZeroDivisorDatum P F ord) (hT : Z.T = B.Tplaces) :
    FibreOverZeroEq c ε X.toFiniteMapData (B.placePoint '' (Z.T : Set P)) :=
  dChartLineBundleRollup_fibre ord X B Z hT

def dChartLineBundleClusterConsumerRows : List (String × String × String) :=
  [ ("chart datum fibre", "PROVED", "dChartLineBundleClusterConsumer_fibre") ]

theorem dChartLineBundleClusterConsumerRows_length : dChartLineBundleClusterConsumerRows.length = 1 := rfl

#check dChartLineBundleClusterConsumer_fibre
#check dChartLineBundleClusterConsumerRows_length

end LeanFormal.IUT.XiFPaper.Mzk1DChartLineBundleClusterConsumerActual
end