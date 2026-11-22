import tmp.sheaf.xif.paper.S2218RangePairTransitiveActual
import tmp.sheaf.xif.paper.S2203D5RangeActual
import tmp.sheaf.xif.paper.S1987D5LargeImageFiveActual
import tmp.sheaf.xif.paper.S1982D5FiveActual
import tmp.sheaf.xif.paper.S1725SourceTorsionFPrimeActual
import tmp.sheaf.xif.paper.S1720SourceArithmeticActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2221AffinePairTransitivityActual

open LeanFormal.IUT.XiFPaper.S2218RangePairTransitiveActual
open LeanFormal.IUT.XiFPaper.S2203D5RangeActual
open LeanFormal.IUT.XiFPaper.S1987D5LargeImageFiveActual
open LeanFormal.IUT.XiFPaper.S1982D5FiveActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S2056Psi5RootsActual
open LeanFormal.IUT.XiFPaper.S2009DicksonActual

/-- Exact actual-range affine-pair transitivity at the selected basis.
This is the S2218 transported action of the actual mod-5 range; it is the
honest form of Galois transitivity on the twelve affine pairs available from
the current representation API. -/
def S2221ActualRangePairTransitiveRequired : Prop :=
  S2218AffinePairTransitive
    (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis).range

/-- Exact equivalence with the S2203 pair-transitivity hypothesis. -/
theorem S2221ActualRangePairTransitiveRequired_iff :
    S2221ActualRangePairTransitiveRequired ↔
      S2203RangePairTransitiveRequired S1982Basis := by
  unfold S2221ActualRangePairTransitiveRequired
  exact S2218RangeAffinePairTransitiveRequired_iff S1982Basis

/-- Conditional actual assembly: the exact range transitivity gives the S2203
pair-transitivity hypothesis. -/
theorem S2221RangePairTransitive_of_actual
    (h : S2221ActualRangePairTransitiveRequired) :
    S2203RangePairTransitiveRequired S1982Basis :=
  S2221ActualRangePairTransitiveRequired_iff.mp h

/-- Conditional D5 assembly from range transitivity and the cycle-type input. -/
theorem S2221D5LargeImageFive_of_actual
    (h : S2221ActualRangePairTransitiveRequired)
    (hcycle : S2203RangeCycleTypeRequired S1982Basis) :
    S1987D5LargeImageFive :=
  S2203D5LargeImageFive_of_rangeHypotheses S1982Basis hcycle
    (S2221RangePairTransitive_of_actual h)

end LeanFormal.IUT.XiFPaper.S2221AffinePairTransitivityActual

end
