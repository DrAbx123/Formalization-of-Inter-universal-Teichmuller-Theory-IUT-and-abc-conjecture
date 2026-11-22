import tmp.sheaf.xif.paper.Mzk1DClusterRollupActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

/-! # D cluster consumer; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1DClusterConsumerActualAdapted

open CategoryTheory AlgebraicGeometry
open NeronModelInfra
open LeanFormal.IUT.XiFPaper.Mzk1GeometricCoreRealStructureActual
open LeanFormal.IUT.XiFPaper.Mzk1GeometricCorePreciseActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreFoundationActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreFoundationActual.SchemeLayer
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreBridgeInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreFiniteMapChartInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1DClusterRollupActual

universe u

variable {R : Type u} [CommRing R] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}

theorem dClusterConsumer_chart (X : FiniteMapChartData c ε) :
    X.toFiniteMapData.m = X.m :=
  (dClusterRollup_chart X).1

def dClusterConsumerRows : List (String × String × String) :=
  [ ("chart identity", "PROVED", "dClusterConsumer_chart") ]

theorem dClusterConsumerRows_length : dClusterConsumerRows.length = 1 := rfl

#check dClusterConsumer_chart
#check dClusterConsumerRows_length

end LeanFormal.IUT.XiFPaper.Mzk1DClusterConsumerActualAdapted
end