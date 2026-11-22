import tmp.sheaf.xif.paper.Mzk1QPilotSHEDoubleImageActual
import tmp.sheaf.xif.paper.S1902ActualThetaHullActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Kummer projection layer: theta image -> q image -> actual Theta hull

This file separates three layers explicitly:
1. theta image in the S1902 root carrier (actual `qroot^(j^2)` values);
2. q image as the `(2l)`-th Kummer power of the label-one theta image,
   proved from the SHE root relation `she_arrow_apply`;
3. genuine hull membership of the theta image via `s1902ImageSet ⊆ s1902Hull`.
The power/Kummer projection is a theorem here, not a named field. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1KummerProjectionLayerV2Actual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1QPilotSHEDoubleImageActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The paper Theta image at label 1 in the root product carrier. -/
def thetaImageOne : S1902Carrier T :=
  thetaPilotImage T (oneThetaLabel l)

/-- The `(2l)`-th Kummer power map on the S1902 root carrier. -/
def kummerProjection (x : S1902Carrier T) : S1902Carrier T :=
  fun b => x b ^ (2 * l.value)

/-- The realized q-pilot image in the S1902 carrier. -/
def qImageInS1902 : S1902Carrier T :=
  completionToRootExtension T (qPilotCompletionImage T)

/-- The q-pilot image is the Kummer projection of the label-one theta image
(SHE root relation; proved, not named). -/
theorem qImageInS1902_eq_kummerProjection :
    qImageInS1902 T = kummerProjection T (thetaImageOne T) := by
  funext b
  simpa [qImageInS1902, kummerProjection, thetaImageOne] using she_arrow_apply T b

/-- The label-one theta image belongs to the actual finite theta image set. -/
theorem thetaImageOne_mem_imageSet :
    thetaImageOne T ∈ s1902ImageSet T := by
  unfold thetaImageOne thetaPilotImage s1902ImageSet rootExtensionProductThetaImageSet
  exact Set.mem_range_self (oneThetaLabel l)

/-- The label-one theta image belongs to the actual Theta hull. -/
theorem thetaImageOne_mem_hull : thetaImageOne T ∈ s1902Hull T :=
  s1902ImageSet_subset_hull (T := T) (thetaImageOne_mem_imageSet T)

end LeanFormal.IUT.XiFPaper.Mzk1KummerProjectionLayerV2Actual

end
