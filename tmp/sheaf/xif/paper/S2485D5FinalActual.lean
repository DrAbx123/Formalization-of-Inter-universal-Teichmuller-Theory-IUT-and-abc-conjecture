import tmp.sheaf.xif.paper.S2480CycleTypeRepairActual
import tmp.sheaf.xif.paper.S2472D5GateActual
import tmp.sheaf.xif.paper.S2440RangePairTransitiveSubagentActual
import tmp.sheaf.xif.paper.S1987D5LargeImageFiveActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2485D5FinalActual

open LeanFormal.IUT.XiFPaper.S2480CycleTypeRepairActual
open LeanFormal.IUT.XiFPaper.S2472D5GateActual
open LeanFormal.IUT.XiFPaper.S2440RangePairTransitiveSubagentActual
open LeanFormal.IUT.XiFPaper.S1987D5LargeImageFiveActual
open LeanFormal.IUT.XiFPaper.S2203D5RangeActual
open LeanFormal.IUT.XiFPaper.S1982D5FiveActual
open LeanFormal.IUT.XiFPaper.S2009DicksonActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual

/-- Exact D5 missing, split into the two actual targets. -/
def S2485ExactMissing : Prop :=
  S2472PairRequired ∧ S2480FirstMissing

/-- D5 target from pair transitivity and the minimal cycle-type element. -/
theorem S2485D5LargeImageFive_of_exact
    (h : S2485ExactMissing) : S1987D5LargeImageFive :=
  S2480D5LargeImageFive_of_firstMissing_and_pair h.2 h.1

/-- Pair transitivity remains the actual range target. -/
theorem S2485Pair_of_imageTail
    (h : S1725ImageTail S1987Five S1982Basis) : S2472PairRequired :=
  S2472Pair_of_imageTail h

/-- Pair transitivity remains implied by a twelve-cycle in the range. -/
theorem S2485Pair_of_twelveCycle
    (h : S2440TwelveCycleInputRequired) : S2472PairRequired :=
  S2472Pair_of_twelveCycle h

/-- Cycle type missing is precisely S2485's second component. -/
theorem S2485CycleFirstMissing_iff :
    S2480FirstMissing ↔ S2480Target :=
  S2480FirstMissing_iff_target

end LeanFormal.IUT.XiFPaper.S2485D5FinalActual

end
