import tmp.sheaf.xif.paper.Mzk1DChartCluster4Actual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

/-! # D chart cluster 10; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1DChartCluster10Actual

open CategoryTheory AlgebraicGeometry
open NeronModelInfra
open LeanFormal.IUT.XiFPaper.Mzk1GeometricCoreRealStructureActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreFiniteMapChartInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1DChartCluster4Actual

universe u

variable {R : Type u} [CommRing R] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}

theorem dChartCluster10_m (X : FiniteMapChartData c ε) :
    X.toFiniteMapData.m = X.m :=
  (dChartCluster4_bundle X).1

def dChartCluster10Rows : List (String × String × String) :=
  [ ("chart m", "PROVED", "dChartCluster10_m") ]

theorem dChartCluster10Rows_length : dChartCluster10Rows.length = 1 := rfl

#check dChartCluster10_m
#check dChartCluster10Rows_length

end LeanFormal.IUT.XiFPaper.Mzk1DChartCluster10Actual
end