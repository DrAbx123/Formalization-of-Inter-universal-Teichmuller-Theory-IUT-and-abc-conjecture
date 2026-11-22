import tmp.sheaf.xif.paper.Mzk1StepXITripleScaleRegionAlignmentActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi paper region scaling law

Set-level scaling law for the paper comparison region: the scaled union equals the
union of scaled images. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIPaperRegionScalingLawActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXITripleScaleRegionAlignmentActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

theorem paper_region_scaling_law
    (scale : S1902Carrier T → S1902Carrier T) (pt : S1902Carrier T) :
    tripleScaleRegion T scale pt =
      scale '' s1902UnitRegion T ∪ scale '' ({pt} : Set (S1902Carrier T)) := by
  simp [tripleScaleRegion, Set.image_union]

theorem paper_region_scaling_law_singleton
    (scale : S1902Carrier T → S1902Carrier T) (pt : S1902Carrier T) :
    scale '' ({pt} : Set (S1902Carrier T)) = {scale pt} := by
  simp

end LeanFormal.IUT.XiFPaper.Mzk1StepXIPaperRegionScalingLawActual

end
