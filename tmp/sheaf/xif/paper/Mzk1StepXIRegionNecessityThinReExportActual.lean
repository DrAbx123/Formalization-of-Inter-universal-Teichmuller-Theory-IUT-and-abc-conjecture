import tmp.sheaf.xif.paper.Mzk1StepXIRegionNecessitySummaryV2Actual
import tmp.sheaf.xif.paper.Mzk1StepXIComparisonRegionMinimalActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi region-necessity thin re-export V2

Thin re-export of the green region necessity summary. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIRegionNecessityThinReExportActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIRegionNecessitySummaryV2Actual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIComparisonRegionMinimalActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

theorem stepxi_region_necessity_thin (a b c : Nat) :
    minimalComparisonRegion T a b c ⊆ s1902Hull T :=
  minimalComparisonRegion_subset_hull T a b c

theorem stepxi_region_obstruction_thin
    (scale : S1902Carrier T → S1902Carrier T) (pt : S1902Carrier T)
    (h : pt ∉ Set.range scale) : pt ∉ tripleScaleRegion T scale pt :=
  not_mem_tripleScaleRegion_of_not_range T scale pt h

end LeanFormal.IUT.XiFPaper.Mzk1StepXIRegionNecessityThinReExportActual

end
