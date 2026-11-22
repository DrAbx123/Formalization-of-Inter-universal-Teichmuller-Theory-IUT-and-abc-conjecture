import tmp.sheaf.xif.paper.Mzk1DChartClusterRollupActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

/-! # D chart cluster consumer 2; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1DChartClusterConsumer2Actual

open CategoryTheory AlgebraicGeometry
open NeronModelInfra
open LeanFormal.IUT.XiFPaper.Mzk1GeometricCoreRealStructureActual
open LeanFormal.IUT.XiFPaper.Mzk1GeometricCorePreciseActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreFoundationActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreFoundationActual.SchemeLayer
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreBridgeInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreFiniteMapChartInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1DChartClusterRollupActual

universe u

variable {R : Type u} [CommRing R] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}

theorem dChartClusterConsumer2_chart (X : FiniteMapChartData c ε) :
    X.toFiniteMapData.m = X.m := dChartClusterRollup_chart X

def dChartClusterConsumer2Rows : List (String × String × String) :=
  [ ("chart identity", "PROVED", "dChartClusterConsumer2_chart") ]

theorem dChartClusterConsumer2Rows_length : dChartClusterConsumer2Rows.length = 1 := rfl

#check dChartClusterConsumer2_chart
#check dChartClusterConsumer2Rows_length

end LeanFormal.IUT.XiFPaper.Mzk1DChartClusterConsumer2Actual
end