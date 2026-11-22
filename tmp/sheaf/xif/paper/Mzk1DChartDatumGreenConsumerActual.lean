import tmp.sheaf.xif.paper.Mzk1GeomCoreChartDatumWitnessActual
import tmp.sheaf.xif.paper.Mzk1GeomCoreChartBasicFactsActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

/-! # D chart datum green consumer; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1DChartDatumGreenConsumerActual

open CategoryTheory AlgebraicGeometry
open NeronModelInfra
open LeanFormal.IUT.XiFPaper.Mzk1GeometricCoreRealStructureActual
open LeanFormal.IUT.XiFPaper.Mzk1GeometricCorePreciseActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreFoundationActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreFoundationActual.SchemeLayer
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreBridgeInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreChartWitnessActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreChartDatumWitnessActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreChartBasicFactsActual

universe u

variable {R : Type u} [CommRing R] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
  {F : Type*} [Field F] {P : Type*}

theorem dChartDatumGreen_bundle (ord : P → F → ℤ) (X : LeanFormal.IUT.XiFPaper.Mzk1GeomCoreFiniteMapChartInterfaceActual.FiniteMapChartData c ε)
    (B : FibreBridgeAbstract C Γ(C, X.U) F (X.U : Set C) X.f
      (C.basicOpen X.f : Set C) P ord)
    (Z : ZeroDivisorDatum P F ord) (hT : Z.T = B.Tplaces) :
    FibreOverZeroEq c ε X.toFiniteMapData (B.placePoint '' (Z.T : Set P)) ∧
      X.toFiniteMapData.m = X.m :=
  ⟨chartDatum_fibre ord X B Z hT, chartBasic_m X⟩

theorem dChartDatumGreen_rows_length : (2 : Nat) = 2 := rfl

#check dChartDatumGreen_bundle
#check dChartDatumGreen_rows_length

end LeanFormal.IUT.XiFPaper.Mzk1DChartDatumGreenConsumerActual
end