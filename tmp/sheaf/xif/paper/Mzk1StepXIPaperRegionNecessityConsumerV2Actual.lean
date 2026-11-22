import tmp.sheaf.xif.paper.Mzk1StepXIRegionNecessitySummaryV2Actual
import tmp.sheaf.xif.paper.Mzk1StepXIComparisonRegionMinimalActual
import tmp.sheaf.xif.paper.Mzk1StepXITripleScaleRegionAlignmentActual
import tmp.sheaf.xif.paper.Mzk1StepXIGap1Gap2BridgeHeightActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi paper region necessity consumer (green-only)

Consumer of the green region-necessity and gap-bridge files; avoids the red
owner files `Mzk1PaperRegionNecessityFinalActual`/`Mzk1A618MachineProofActual`. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIPaperRegionNecessityConsumerV2Actual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIRegionNecessitySummaryV2Actual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIComparisonRegionMinimalActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXITripleScaleRegionAlignmentActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIGap1Gap2BridgeHeightActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

theorem stepxi_paper_region_necessity (a b c : Nat) :
    minimalComparisonRegion T a b c ⊆ s1902Hull T :=
  minimalComparisonRegion_subset_hull T a b c

theorem stepxi_paper_region_obstruction
    (scale : S1902Carrier T → S1902Carrier T) (pt : S1902Carrier T)
    (h : pt ∉ Set.range scale) : pt ∉ tripleScaleRegion T scale pt :=
  not_mem_tripleScaleRegion_of_not_range T scale pt h

end LeanFormal.IUT.XiFPaper.Mzk1StepXIPaperRegionNecessityConsumerV2Actual

end
