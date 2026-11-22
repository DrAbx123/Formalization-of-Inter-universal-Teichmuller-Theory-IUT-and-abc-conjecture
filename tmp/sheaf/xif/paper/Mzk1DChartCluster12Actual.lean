import tmp.sheaf.xif.paper.Mzk1DChartCluster9Actual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

/-! # D chart cluster 12; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1DChartCluster12Actual

open CategoryTheory AlgebraicGeometry
open NeronModelInfra
open LeanFormal.IUT.XiFPaper.Mzk1GeometricCoreRealStructureActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreFiniteMapChartInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1DChartCluster9Actual

universe u

variable {R : Type u} [CommRing R] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}

theorem dChartCluster12_U (X : FiniteMapChartData c ε) :
    (X.toFiniteMapData.U : Set C) = (Set.range ε.1.base)ᶜ :=
  dChartCluster9_U X

def dChartCluster12Rows : List (String × String × String) :=
  [ ("chart U", "PROVED", "dChartCluster12_U") ]

theorem dChartCluster12Rows_length : dChartCluster12Rows.length = 1 := rfl

#check dChartCluster12_U
#check dChartCluster12Rows_length

end LeanFormal.IUT.XiFPaper.Mzk1DChartCluster12Actual
end