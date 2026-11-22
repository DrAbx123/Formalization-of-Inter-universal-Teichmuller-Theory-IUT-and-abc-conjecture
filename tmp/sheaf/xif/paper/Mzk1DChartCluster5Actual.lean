import tmp.sheaf.xif.paper.Mzk1GeomCoreChartBasicFactsActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

/-! # D chart cluster 5; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1DChartCluster5Actual

open CategoryTheory AlgebraicGeometry
open NeronModelInfra
open LeanFormal.IUT.XiFPaper.Mzk1GeometricCoreRealStructureActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreFiniteMapChartInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreChartBasicFactsActual

universe u

variable {R : Type u} [CommRing R] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}

theorem dChartCluster5_chart (X : FiniteMapChartData c ε) :
    X.toFiniteMapData.m = X.m := chartBasic_m X

theorem dChartCluster5_U (X : FiniteMapChartData c ε) :
    (X.toFiniteMapData.U : Set C) = (Set.range ε.1.base)ᶜ := chartBasic_U X

def dChartCluster5Rows : List (String × String × String) :=
  [ ("chart m", "PROVED", "dChartCluster5_chart"),
    ("chart U", "PROVED", "dChartCluster5_U") ]

theorem dChartCluster5Rows_length : dChartCluster5Rows.length = 2 := rfl

#check dChartCluster5_chart
#check dChartCluster5Rows_length

end LeanFormal.IUT.XiFPaper.Mzk1DChartCluster5Actual
end