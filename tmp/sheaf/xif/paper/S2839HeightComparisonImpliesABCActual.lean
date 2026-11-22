import tmp.sheaf.xif.paper.S2836AdditiveBridgeActual
import tmp.sheaf.xif.paper.S2833S2800HregionActual
import LeanFormal.IUT.ABCBridge.Arithmetic.ABCHeightArithmeticWeightComparison

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2800LineBundleCor312BridgeActual
open LeanFormal.IUT.XiFPaper.S2836AdditiveBridgeActual
open LeanFormal.IUT.XiFPaper.S2808S2800HalfNormalizedActual
open LeanFormal.IUT.XiFPaper.S2833S2800HregionActual
open LeanFormal.IUT.XiFPaper.S2781PointedLineBundleRegionActual
open LeanFormal.IUT.XiFPaper.S2792NormalizedLineBundleBridge
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000

namespace LeanFormal.IUT.XiFPaper.S2839HeightComparisonImpliesABCActual

abbrev S2839W : IQHullLogVolumeInterface (S2800Carrier S2833l) :=
  S2808HalfIQHull S2833l 1

/-- The exact additive height comparison requested for the half-normalized
pointed region. -/
def S2839HeightComparisonAdditive : Prop :=
  forall (eps : Real), 0 < eps -> exists A : Real,
    forall a b c : Nat, IsABCTriple a b c ->
      Height.logHeight₁ (abcRationalPoint a c)
        <= (1 + eps) * (S2839W.logVolume
            (normalizedComparisonRegion S2839W
              (S2781LogShellPoint S2833l) a b c)).toReal
          + A

/-- The additive height comparison implies the ABC height-weight additive
contract.  Thus it is at least as hard as ABC; the missing lemma is the full
ABC height bound, not a local IUT IV bookkeeping identity. -/
theorem S2839_heightComparison_implies_ABCHeightWeightAdditiveBoundV2
    (h : S2839HeightComparisonAdditive) :
    ABCHeightWeightAdditiveBoundV2 := by
  intro eps heps
  obtain ⟨A, hA⟩ := h eps heps
  refine ⟨(1 + eps) * S2792D + A, ?_⟩
  intro a b c habc
  have h1 := hA a b c habc
  have hregion := S2833_region_volume a b c habc
  have hbound := S2792_regionVolume_le_weight_add_D a b c habc
  have hnn : 0 <= 1 + eps := by linarith
  have hscaled := mul_le_mul_of_nonneg_left hbound hnn
  rw [hregion] at h1
  nlinarith

#check S2839W
#check S2839HeightComparisonAdditive
#check S2839_heightComparison_implies_ABCHeightWeightAdditiveBoundV2
#print axioms S2839_heightComparison_implies_ABCHeightWeightAdditiveBoundV2

end LeanFormal.IUT.XiFPaper.S2839HeightComparisonImpliesABCActual
end
