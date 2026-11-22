import tmp.sheaf.xif.paper.Mzk1BridgeInterfaceAssemblyActual
import tmp.sheaf.xif.paper.Mzk1E5UndilatedABCBridgeActualV2
import tmp.sheaf.xif.paper.S3131PaperRouteHeightReductionActual
import tmp.sheaf.xif.paper.S3131PaperRouteRegionReductionActual
import tmp.sheaf.xif.paper.S3131PaperRouteFieldStatementsActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1ChainBridgeFamiliesActual — bridge/undilated conjunction chains

Genuine new conjunctions combining EXIT0 consumers:
* a per-epsilon comparison family gives both ABCConjecture and the additive
  height-weight bound;
* the undilated (b)+(c) bounds give ABCConjecture together with the height and
  region-volume families.
No new paper input; no closure; gate NOT PASSED; registry 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1ChainBridgeFamiliesActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1BridgeInterfaceAssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1E5UndilatedABCBridgeActualV2
open LeanFormal.IUT.XiFPaper.S3131PaperRouteHeightReductionActual
open LeanFormal.IUT.XiFPaper.S3131PaperRouteRegionReductionActual
open LeanFormal.IUT.XiFPaper.S3131PaperRouteFieldStatementsActual
open LeanFormal.IUT.XiFPaper.Cor312ComparisonRegionV2Actual

universe u

/-- Comparison family -> ABC and the additive height-weight bound together. -/
theorem abc_and_heightBound_of_family (X : Type u) (W : IQHullLogVolumeInterface X)
    (C : ∀ eps : ℝ, 0 < eps → Cor312EpsilonArithmeticComparison W eps) :
    ABCConjecture ∧
      (∀ eps : ℝ, 0 < eps → ∃ A : ℝ, ∀ a b c : Nat, IsABCTriple a b c →
        Height.logHeight₁ (abcRationalPoint a c) ≤
          (1 + eps) * arithmeticWeight (abcRationalPoint a c) + A) :=
  ⟨abcConjecture_of_comparisonFamily X W C,
   heightBound_of_comparisonFamily X W C⟩

/-- Undilated (b)+(c) bounds -> ABC, height family and region family together. -/
theorem undilated_abc_and_families {X : Type u} {W : IQHullLogVolumeInterface X}
    {pt : Nat → Nat → Nat → X}
    (hb : UndilatedHeightBound W pt) (hc : UndilatedRegionBound W pt) :
    ABCConjecture ∧ HeightComparisonFamily W pt ∧ RegionVolumeFamily W pt :=
  ⟨abcConjecture_of_undilatedBounds hb hc,
   heightComparisonFamily_of_undilatedBound hb,
   regionVolumeFamily_of_undilatedBound hc⟩

end LeanFormal.IUT.XiFPaper.Mzk1ChainBridgeFamiliesActual

end
