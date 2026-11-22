import tmp.sheaf.xif.paper.Mzk1StepXIObstructionTripleScaleActual
import tmp.sheaf.xif.paper.Mzk1StepXITripleScaleRegionAlignmentActual
import tmp.sheaf.xif.paper.Mzk1StepXIComparisonRegionMinimalActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi region necessity summary

Summary of the region necessity obstruction and the minimal comparison region's
containment in the hull. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIRegionNecessitySummaryV2Actual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIObstructionTripleScaleActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXITripleScaleRegionAlignmentActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIComparisonRegionMinimalActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

theorem stepxi_region_necessity_summary
    (scale : S1902Carrier T → S1902Carrier T) (pt : S1902Carrier T)
    (h : pt ∉ Set.range scale) :
    (pt ∉ tripleScaleRegion T scale pt) ∧
      (∀ a b c : Nat, minimalComparisonRegion T a b c ⊆ s1902Hull T) :=
  ⟨not_mem_tripleScaleRegion_of_not_range T scale pt h,
    fun a b c => minimalComparisonRegion_subset_hull T a b c⟩

end LeanFormal.IUT.XiFPaper.Mzk1StepXIRegionNecessitySummaryV2Actual

end
