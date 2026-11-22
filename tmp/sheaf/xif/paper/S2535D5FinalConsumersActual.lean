import tmp.sheaf.xif.paper.S2520RootCycleTransferActual
import tmp.sheaf.xif.paper.S2480CycleTypeRepairActual
import tmp.sheaf.xif.paper.S2440RangePairTransitiveSubagentActual
import tmp.sheaf.xif.paper.S2378ActualPairTransitiveActual
import tmp.sheaf.xif.paper.S1987D5LargeImageFiveActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2535D5FinalConsumersActual

open LeanFormal.IUT.XiFPaper.S2520RootCycleTransferActual
open LeanFormal.IUT.XiFPaper.S2480CycleTypeRepairActual
open LeanFormal.IUT.XiFPaper.S2440RangePairTransitiveSubagentActual
open LeanFormal.IUT.XiFPaper.S2378ActualPairTransitiveActual
open LeanFormal.IUT.XiFPaper.S2203D5RangeActual
open LeanFormal.IUT.XiFPaper.S2132FrobCycleActual
open LeanFormal.IUT.XiFPaper.S1987D5LargeImageFiveActual
open LeanFormal.IUT.XiFPaper.S1982D5FiveActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual

/-- The two remaining D5 arithmetic inputs. -/
def S2535D5ExactMissing : Prop :=
  S2132FrobInducesPairCycleType ∧ S2203RangePairTransitiveRequired S1982Basis

/-- D5 target from the S2132 cycle-type input and range pair transitivity. -/
theorem S2535D5LargeImageFive_of_exact
    (h : S2535D5ExactMissing) : S1987D5LargeImageFive :=
  S2480D5LargeImageFive_of_firstMissing_and_pair
    (S2520S2480FirstMissing_of_S2132 h.1) h.2

/-- Pair transitivity from the image-tail input. -/
theorem S2535Pair_of_imageTail
    (h : S1725ImageTail S1987Five S1982Basis) :
    S2203RangePairTransitiveRequired S1982Basis :=
  S2440RangePairTransitive_of_imageTail h

/-- Pair transitivity from a twelve-cycle in the actual range. -/
theorem S2535Pair_of_twelveCycle
    (h : S2440TwelveCycleInputRequired) :
    S2203RangePairTransitiveRequired S1982Basis :=
  S2440RangePairTransitive_of_twelveCycle h

/-- Pair transitivity from range = top. -/
theorem S2535Pair_of_rangeTop
    (h : S2378RangeTopRequired) :
    S2203RangePairTransitiveRequired S1982Basis :=
  S2378PairTransitive_of_rangeTop h

end LeanFormal.IUT.XiFPaper.S2535D5FinalConsumersActual

end
