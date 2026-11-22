import tmp.sheaf.xif.paper.Mzk1StepXIObstructionTripleScaleActual
import tmp.sheaf.xif.paper.Mzk1StepXITripleScaleRegionAlignmentActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi obstruction consumer (thin re-export)

Re-exports the A618 triple-scale obstruction under a downstream consumer name. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIObstructionConsumerV2Actual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIObstructionTripleScaleActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXITripleScaleRegionAlignmentActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

theorem stepxi_obstruction_consumer
    (scale : S1902Carrier T → S1902Carrier T) (pt : S1902Carrier T)
    (h : pt ∉ Set.range scale) :
    pt ∉ tripleScaleRegion T scale pt :=
  not_mem_tripleScaleRegion_of_not_range T scale pt h

theorem stepxi_obstruction_range_consumer
    (scale : S1902Carrier T → S1902Carrier T) (pt : S1902Carrier T) :
    tripleScaleRegion T scale pt ⊆ Set.range scale :=
  tripleScaleRegion_subset_range T scale pt

end LeanFormal.IUT.XiFPaper.Mzk1StepXIObstructionConsumerV2Actual

end
