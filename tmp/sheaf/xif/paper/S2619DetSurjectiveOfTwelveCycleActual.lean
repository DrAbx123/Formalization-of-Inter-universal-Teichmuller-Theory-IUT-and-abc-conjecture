import tmp.sheaf.xif.paper.S2618RangeDetActual
import tmp.sheaf.xif.paper.S2440RangePairTransitiveSubagentActual

noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 200000

namespace LeanFormal.IUT.XiFPaper.S2619DetSurjectiveOfTwelveCycleActual

open LeanFormal.IUT.XiFPaper.S2618RangeDetActual
open LeanFormal.IUT.XiFPaper.S2613DetCyclotomicInterfaceActual
open LeanFormal.IUT.XiFPaper.S2440RangePairTransitiveSubagentActual

/-- The S2440 twelve-cycle input implies determinant surjectivity on the actual range. -/
theorem S2619DetSurjective_of_twelveCycleInput
    (h : S2440TwelveCycleInputRequired) :
    S2613DetSurjectiveRemaining := by
  rcases h with ⟨h, hh, hc⟩
  exact S2618DetSurjective_of_range_cycle12 h hh hc

end LeanFormal.IUT.XiFPaper.S2619DetSurjectiveOfTwelveCycleActual
end