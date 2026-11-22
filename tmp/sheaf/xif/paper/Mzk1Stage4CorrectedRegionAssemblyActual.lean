import tmp.sheaf.xif.paper.Mzk1CorrectedRegionGap1Actual
import tmp.sheaf.xif.paper.Mzk1Stage4NullSetAssemblyActual

/-! # Mzk1Stage4CorrectedRegionAssemblyActual (stage4 lane; parameterized B1 assembly)

A673 module: parameterized B1 assembly for the corrected region — GIVEN the point-image
nullity hypothesis `rootExtensionProductHaar (badInvScale e '' {point}) = 0`, the measure
of the corrected paper region equals the measure of the scaled unit region.  This is the
exact bridge needed to apply the mainline unit-region product law before the log-form
assembly (B2/B3).  The point nullity is an EXPLICIT parameter (hull lane supplies it).
Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4CorrectedRegionAssemblyActual

open MeasureTheory
open scoped ENNReal Pointwise
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1CorrectedRegionGap1Actual
open LeanFormal.IUT.XiFPaper.Mzk1Stage4NullSetAssemblyActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1CarrierBadInvScaleProductActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.Mzk1HaarScalingOneDimActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The corrected exponent function `e_b = v_{p_b}(a+b+c+1)` of the corrected region. -/
def correctedExponent (a b c : Nat) : Bad (nativePlaceSelection T) → Nat :=
  fun bBad => padicValNat (qVFamTensorP T bBad) (a + b + c + 1)

/-- The corrected paper region is the union of the scaled unit region and the scaled
point image. -/
theorem correctedPaperRegion_eq_union
    (point : Nat → Nat → Nat → S1902Carrier T) (a b c : Nat) :
    correctedPaperRegion T point a b c =
      Mzk1CarrierBadInvScaleLawActual.badInvScale T (correctedExponent T a b c) '' s1902UnitRegion T ∪
        Mzk1CarrierBadInvScaleLawActual.badInvScale T (correctedExponent T a b c) '' {point a b c} := by
  unfold correctedPaperRegion correctedRegion correctedExponent
  rw [Set.image_union]

/-- Parameterized B1 assembly: if the scaled point image is null, the corrected region
has the measure of the scaled unit region. -/
theorem correctedPaperRegion_measure_of_null_point
    (point : Nat → Nat → Nat → S1902Carrier T) (a b c : Nat)
    (hpt : rootExtensionProductHaar T
      (Mzk1CarrierBadInvScaleLawActual.badInvScale T (correctedExponent T a b c) '' {point a b c}) = 0) :
    rootExtensionProductHaar T (correctedPaperRegion T point a b c) =
      rootExtensionProductHaar T
        (Mzk1CarrierBadInvScaleLawActual.badInvScale T (correctedExponent T a b c) '' s1902UnitRegion T) := by
  unfold correctedPaperRegion correctedRegion correctedExponent
  rw [Set.image_union]
  exact measure_union_eq_left_of_null hpt

/-- Assembly status rows. -/
def assemblyRows : List (String × String) :=
  [ ("region decomposition", "correctedPaperRegion = scaled unit ∪ scaled point image (PROVED)")
  , ("B1 parameterized", "null point image ⇒ measure = scaled-unit measure (PROVED here)")
  , ("B1 concrete", "rootExtensionProductHaar (scaled {point}) = 0 — hull lane")
  , ("next", "apply corrected_unitRegion_measure (product law) then B2/B3 log form")
  ]

/-- The assembly record has four rows. -/
theorem assemblyRows_length : assemblyRows.length = 4 := rfl

#check correctedPaperRegion_eq_union
#check correctedPaperRegion_measure_of_null_point
#check assemblyRows_length

end LeanFormal.IUT.XiFPaper.Mzk1Stage4CorrectedRegionAssemblyActual
end
