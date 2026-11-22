import tmp.sheaf.xif.paper.Mzk1DChartCluster4Actual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

/-! # D chart cluster 9; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1DChartCluster9Actual

open CategoryTheory AlgebraicGeometry
open NeronModelInfra
open LeanFormal.IUT.XiFPaper.Mzk1GeometricCoreRealStructureActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreFiniteMapChartInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1DChartCluster4Actual

universe u

variable {R : Type u} [CommRing R] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}

theorem dChartCluster9_U (X : FiniteMapChartData c ε) :
    (X.toFiniteMapData.U : Set C) = (Set.range ε.1.base)ᶜ :=
  (dChartCluster4_bundle X).2

def dChartCluster9Rows : List (String × String × String) :=
  [ ("chart U", "PROVED", "dChartCluster9_U") ]

theorem dChartCluster9Rows_length : dChartCluster9Rows.length = 1 := rfl

#check dChartCluster9_U
#check dChartCluster9Rows_length

end LeanFormal.IUT.XiFPaper.Mzk1DChartCluster9Actual
end