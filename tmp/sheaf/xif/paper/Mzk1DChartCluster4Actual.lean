import tmp.sheaf.xif.paper.Mzk1GeomCoreChartBasicFactsActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

/-! # D chart cluster 4; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1DChartCluster4Actual

open CategoryTheory AlgebraicGeometry
open NeronModelInfra
open LeanFormal.IUT.XiFPaper.Mzk1GeometricCoreRealStructureActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreFiniteMapChartInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreChartBasicFactsActual

universe u

variable {R : Type u} [CommRing R] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}

theorem dChartCluster4_bundle (X : FiniteMapChartData c ε) :
    X.toFiniteMapData.m = X.m ∧
      ((X.toFiniteMapData.U : Set C) = (Set.range ε.1.base)ᶜ) :=
  chartBasic_bundle X

def dChartCluster4Rows : List (String × String × String) :=
  [ ("chart bundle", "PROVED", "dChartCluster4_bundle") ]

theorem dChartCluster4Rows_length : dChartCluster4Rows.length = 1 := rfl

#check dChartCluster4_bundle
#check dChartCluster4Rows_length

end LeanFormal.IUT.XiFPaper.Mzk1DChartCluster4Actual
end