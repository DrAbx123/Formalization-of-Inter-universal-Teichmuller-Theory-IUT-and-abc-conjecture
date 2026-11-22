import tmp.sheaf.xif.paper.Mzk1GeomCoreChartBasicFactsActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

/-! # D chart cluster 7; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1DChartCluster7Actual

open CategoryTheory AlgebraicGeometry
open NeronModelInfra
open LeanFormal.IUT.XiFPaper.Mzk1GeometricCoreRealStructureActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreFiniteMapChartInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreChartBasicFactsActual

universe u

variable {R : Type u} [CommRing R] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}

theorem dChartCluster7_bundle (X : FiniteMapChartData c ε) :
    X.toFiniteMapData.m = X.m := chartBasic_m X

def dChartCluster7Rows : List (String × String × String) :=
  [ ("chart m", "PROVED", "dChartCluster7_bundle") ]

theorem dChartCluster7Rows_length : dChartCluster7Rows.length = 1 := rfl

#check dChartCluster7_bundle
#check dChartCluster7Rows_length

end LeanFormal.IUT.XiFPaper.Mzk1DChartCluster7Actual
end