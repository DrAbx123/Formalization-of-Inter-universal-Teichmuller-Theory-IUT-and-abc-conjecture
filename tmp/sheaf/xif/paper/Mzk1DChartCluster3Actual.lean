import tmp.sheaf.xif.paper.Mzk1DChartClusterRollupActual
import tmp.sheaf.xif.paper.Mzk1GeomCoreChartBasicFactsActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

/-! # D chart cluster 3; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1DChartCluster3Actual

open CategoryTheory AlgebraicGeometry
open NeronModelInfra
open LeanFormal.IUT.XiFPaper.Mzk1GeometricCoreRealStructureActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreFiniteMapChartInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreChartBasicFactsActual
open LeanFormal.IUT.XiFPaper.Mzk1DChartClusterRollupActual

universe u

variable {R : Type u} [CommRing R] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}

theorem dChartCluster3_bundle (X : FiniteMapChartData c ε) :
    X.toFiniteMapData.m = X.m ∧
      ((X.toFiniteMapData.U : Set C) = (Set.range ε.1.base)ᶜ) :=
  ⟨dChartClusterRollup_chart X, chartBasic_U X⟩

def dChartCluster3Rows : List (String × String × String) :=
  [ ("chart m + U", "PROVED", "dChartCluster3_bundle") ]

theorem dChartCluster3Rows_length : dChartCluster3Rows.length = 1 := rfl

#check dChartCluster3_bundle
#check dChartCluster3Rows_length

end LeanFormal.IUT.XiFPaper.Mzk1DChartCluster3Actual
end