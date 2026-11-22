import tmp.sheaf.xif.paper.Mzk1DChartDatumWitnessGreenActual
import tmp.sheaf.xif.paper.Mzk1GeomCoreChartBasicFactsActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

/-! # D chart datum cluster 2; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1DChartDatumCluster2Actual

open CategoryTheory AlgebraicGeometry
open NeronModelInfra
open LeanFormal.IUT.XiFPaper.Mzk1GeometricCoreRealStructureActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreChartBasicFactsActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreFiniteMapChartInterfaceActual

universe u

variable {R : Type u} [CommRing R] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}

theorem dChartDatumCluster2_chart (X : FiniteMapChartData c ε) :
    X.toFiniteMapData.m = X.m := chartBasic_m X

theorem dChartDatumCluster2_mem (X : FiniteMapChartData c ε) (x : C) :
    x ∈ X.toFiniteMapData.U ↔ x ∉ Set.range ε.1.base := chartBasic_mem_iff X x

def dChartDatumCluster2Rows : List (String × String × String) :=
  [ ("chart m", "PROVED", "dChartDatumCluster2_chart"),
    ("mem U", "PROVED", "dChartDatumCluster2_mem") ]

theorem dChartDatumCluster2Rows_length : dChartDatumCluster2Rows.length = 2 := rfl

#check dChartDatumCluster2_chart
#check dChartDatumCluster2Rows_length

end LeanFormal.IUT.XiFPaper.Mzk1DChartDatumCluster2Actual
end