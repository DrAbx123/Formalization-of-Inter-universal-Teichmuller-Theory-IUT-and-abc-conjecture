import tmp.sheaf.xif.paper.S2470PairTransitiveFinalActual
import tmp.sheaf.xif.paper.S2481PairTransitiveHardActual
import tmp.sheaf.xif.paper.S2535D5FinalConsumersActual
import tmp.sheaf.xif.paper.S1987D5LargeImageFiveActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2545D5ArithmeticMissingActual

open LeanFormal.IUT.XiFPaper.S2470PairTransitiveFinalActual
open LeanFormal.IUT.XiFPaper.S2481PairTransitiveHardActual
open LeanFormal.IUT.XiFPaper.S2535D5FinalConsumersActual
open LeanFormal.IUT.XiFPaper.S2203D5RangeActual
open LeanFormal.IUT.XiFPaper.S2132FrobCycleActual
open LeanFormal.IUT.XiFPaper.S1987D5LargeImageFiveActual
open LeanFormal.IUT.XiFPaper.S1982D5FiveActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual

/-- Exact arithmetic missing for pair transitivity via the 12-cycle route. -/
def S2545PairExactMissing : Prop :=
  S2470ResidueCertificateRequired ∧ S2470RootToRangeTransport

/-- Exact arithmetic missing for the (10,2) cycle-type route. -/
def S2545CycleExactMissing : Prop :=
  S2132FrobInducesPairCycleType

theorem S2545Pair_of_exact
    (h : S2545PairExactMissing) :
    S2203RangePairTransitiveRequired S1982Basis :=
  S2470Target_of_residueData_and_transport (Classical.choice h.1) h.2

/-- With both arithmetic inputs, D5 is actual. -/
theorem S2545D5LargeImageFive_of_arithmetic
    (hp : S2545PairExactMissing)
    (hc : S2545CycleExactMissing) : S1987D5LargeImageFive :=
  S2535D5LargeImageFive_of_exact ⟨hc, S2545Pair_of_exact hp⟩

end LeanFormal.IUT.XiFPaper.S2545D5ArithmeticMissingActual

end
