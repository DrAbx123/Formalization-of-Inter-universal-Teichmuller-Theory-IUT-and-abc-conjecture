import tmp.sheaf.xif.paper.Mzk1DChartCluster11Actual
import tmp.sheaf.xif.paper.Mzk1DChartCluster12Actual
import tmp.sheaf.xif.paper.Mzk1DChartCluster13Actual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

/-!
# Mzk1ChainDChartActualAdapted (adapted copy, A475 reuse) — chained D-chart cluster consumers

Chains EXIT0 D-chart clusters 11/12/13: the finite-map chart data satisfies the
m/U identification.  No new math; no closure; gate NOT PASSED; registry 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1ChainDChartActualAdapted

open CategoryTheory AlgebraicGeometry
open NeronModelInfra
open LeanFormal.IUT.XiFPaper.Mzk1GeometricCoreRealStructureActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreFiniteMapChartInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1DChartCluster11Actual
open LeanFormal.IUT.XiFPaper.Mzk1DChartCluster12Actual
open LeanFormal.IUT.XiFPaper.Mzk1DChartCluster13Actual

universe u

variable {R : Type u} [CommRing R] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}

theorem dChartChain_all (X : FiniteMapChartData c ε) :
    X.toFiniteMapData.m = X.m ∧
      ((X.toFiniteMapData.U : Set C) = (Set.range ε.1.base)ᶜ) := by
  exact ⟨dChartCluster13_m X, dChartCluster13_U X⟩

def chainDChartRows : List (String × String × String) :=
  [ ("chart m/U chain", "dChartChain_all", "PROVED (reuse)"),
    ("scope", "no new math; no closure; gate NOT PASSED", "INTEGRITY") ]

theorem chainDChartRows_length : chainDChartRows.length = 2 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1ChainDChartActualAdapted

end
