import tmp.sheaf.xif.paper.Mzk1DChartDatumWitnessGreenActual
import tmp.sheaf.xif.paper.Mzk1DChartClusterRollupActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

/-! # D chart cluster 2; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1DChartCluster2Actual

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
open LeanFormal.IUT.XiFPaper.Mzk1DChartClusterRollupActual

universe u

variable {R : Type u} [CommRing R] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
  {F : Type*} [Field F] {P : Type*}

theorem dChartCluster2_chart (X : FiniteMapChartData c ε) :
    X.toFiniteMapData.m = X.m := dChartClusterRollup_chart X

def dChartCluster2Rows : List (String × String × String) :=
  [ ("chart identity", "PROVED", "dChartCluster2_chart") ]

theorem dChartCluster2Rows_length : dChartCluster2Rows.length = 1 := rfl

#check dChartCluster2_chart
#check dChartCluster2Rows_length

end LeanFormal.IUT.XiFPaper.Mzk1DChartCluster2Actual
end