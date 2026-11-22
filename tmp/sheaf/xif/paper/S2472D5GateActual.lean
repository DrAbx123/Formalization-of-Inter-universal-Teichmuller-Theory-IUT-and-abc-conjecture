import tmp.sheaf.xif.paper.S2449D5FinalStatusActual
import tmp.sheaf.xif.paper.S2440RangePairTransitiveSubagentActual
import tmp.sheaf.xif.paper.S2203D5RangeActual
import tmp.sheaf.xif.paper.S1987D5LargeImageFiveActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2472D5GateActual

open LeanFormal.IUT.XiFPaper.S2449D5FinalStatusActual
open LeanFormal.IUT.XiFPaper.S2440RangePairTransitiveSubagentActual
open LeanFormal.IUT.XiFPaper.S2203D5RangeActual
open LeanFormal.IUT.XiFPaper.S1987D5LargeImageFiveActual
open LeanFormal.IUT.XiFPaper.S1982D5FiveActual
open LeanFormal.IUT.XiFPaper.S2009DicksonActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual

/-- Actual range pair-transitivity requirement at S1982Basis. -/
def S2472PairRequired : Prop :=
  S2203RangePairTransitiveRequired S1982Basis

/-- Actual range cycle-type requirement at S1982Basis. -/
def S2472CycleRequired : Prop :=
  S2203RangeCycleTypeRequired S1982Basis

/-- Exact D5 missing: pair transitivity and cycle type, both actual targets. -/
def S2472ExactMissing : Prop :=
  S2472PairRequired ∧ S2472CycleRequired

/-- Conditional D5 target from the exact missing pair/cycle data. -/
theorem S2472D5LargeImageFive_of_exact
    (h : S2472ExactMissing) : S1987D5LargeImageFive :=
  S2449D5LargeImageFive_of_exact h

/-- Pair transitivity from the image-tail input. -/
theorem S2472Pair_of_imageTail
    (h : S1725ImageTail S1987Five S1982Basis) : S2472PairRequired :=
  S2440RangePairTransitive_of_imageTail h

/-- Pair transitivity from the twelve-cycle input. -/
theorem S2472Pair_of_twelveCycle
    (h : S2440TwelveCycleInputRequired) : S2472PairRequired :=
  S2440RangePairTransitive_of_twelveCycle h

/-- Cycle type remains the exact Dedekind-Frobenius target. -/
theorem S2472CycleRequired_iff :
    S2472CycleRequired ↔
      HasCycleType102
        (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis).range :=
  Iff.rfl

end LeanFormal.IUT.XiFPaper.S2472D5GateActual

end
