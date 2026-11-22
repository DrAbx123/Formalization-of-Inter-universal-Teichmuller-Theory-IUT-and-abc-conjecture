import tmp.sheaf.xif.paper.Mzk1DChartCluster4Actual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

/-! # D chart cluster 11; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1DChartCluster11Actual

open CategoryTheory AlgebraicGeometry
open NeronModelInfra
open LeanFormal.IUT.XiFPaper.Mzk1GeometricCoreRealStructureActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreFiniteMapChartInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1DChartCluster4Actual

universe u

variable {R : Type u} [CommRing R] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}

theorem dChartCluster11_all (X : FiniteMapChartData c ε) :
    X.toFiniteMapData.m = X.m ∧
      ((X.toFiniteMapData.U : Set C) = (Set.range ε.1.base)ᶜ) :=
  dChartCluster4_bundle X

def dChartCluster11Rows : List (String × String × String) :=
  [ ("chart bundle", "PROVED", "dChartCluster11_all") ]

theorem dChartCluster11Rows_length : dChartCluster11Rows.length = 1 := rfl

#check dChartCluster11_all
#check dChartCluster11Rows_length

end LeanFormal.IUT.XiFPaper.Mzk1DChartCluster11Actual
end