import tmp.sheaf.xif.paper.Mzk1DChartCluster4Actual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

/-! # D chart cluster 13; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1DChartCluster13Actual

open CategoryTheory AlgebraicGeometry
open NeronModelInfra
open LeanFormal.IUT.XiFPaper.Mzk1GeometricCoreRealStructureActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreFiniteMapChartInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1DChartCluster4Actual

universe u

variable {R : Type u} [CommRing R] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}

theorem dChartCluster13_m (X : FiniteMapChartData c ε) :
    X.toFiniteMapData.m = X.m := (dChartCluster4_bundle X).1

theorem dChartCluster13_U (X : FiniteMapChartData c ε) :
    (X.toFiniteMapData.U : Set C) = (Set.range ε.1.base)ᶜ := (dChartCluster4_bundle X).2

def dChartCluster13Rows : List (String × String × String) :=
  [ ("chart m", "PROVED", "dChartCluster13_m"),
    ("chart U", "PROVED", "dChartCluster13_U") ]

theorem dChartCluster13Rows_length : dChartCluster13Rows.length = 2 := rfl

#check dChartCluster13Rows_length

end LeanFormal.IUT.XiFPaper.Mzk1DChartCluster13Actual
end