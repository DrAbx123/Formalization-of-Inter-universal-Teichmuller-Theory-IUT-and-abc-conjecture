import tmp.sheaf.xif.paper.S2243RangeCompatibilityActual
import tmp.sheaf.xif.paper.S2229RangeTransitivityActual
import tmp.sheaf.xif.paper.S2203D5RangeActual
import tmp.sheaf.xif.paper.S1987D5LargeImageFiveActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2375RangePairTransitiveActual

open LeanFormal.IUT.XiFPaper.S2243RangeCompatibilityActual
open LeanFormal.IUT.XiFPaper.S2229RangeTransitivityActual
open LeanFormal.IUT.XiFPaper.S2218RangePairTransitiveActual
open LeanFormal.IUT.XiFPaper.S2203D5RangeActual
open LeanFormal.IUT.XiFPaper.S1987D5LargeImageFiveActual
open LeanFormal.IUT.XiFPaper.S1982D5FiveActual
open LeanFormal.IUT.XiFPaper.S2009DicksonActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual

/-- The actual Galois transitivity target on the twelve affine pairs. -/
def S2375GaloisPairTransitiveRequired : Prop :=
  S2229GaloisPairTransitive S1982Basis

/-- The actual range pair-transitivity target. -/
def S2375RangePairTransitiveRequired : Prop :=
  S2203RangePairTransitiveRequired S1982Basis

/-- Actual equivalence between Galois transitivity on affine pairs and range
pair transitivity, using the transferred-range identity and S2218. -/
theorem S2375GaloisPairTransitive_iff_range :
    S2375GaloisPairTransitiveRequired ↔
      S2375RangePairTransitiveRequired := by
  unfold S2375GaloisPairTransitiveRequired
    S2375RangePairTransitiveRequired
    S2203RangePairTransitiveRequired
  rw [S2229GaloisPairTransitive_iff]
  rw [S2243TransferredRange_eq S1982Basis]
  exact S2218RangeAffinePairTransitiveRequired_iff S1982Basis

/-- Exact first missing: actual Galois/range pair transitivity. -/
def S2375ExactFirstMissing : Prop :=
  S2375RangePairTransitiveRequired

/-- Conditional D5 assembly from the exact range pair transitivity and the
cycle-type hypothesis. -/
theorem S2375D5LargeImageFive_of_exact
    (h : S2375ExactFirstMissing)
    (hcycle : S2203RangeCycleTypeRequired S1982Basis) :
    S1987D5LargeImageFive :=
  S2203D5LargeImageFive_of_rangeHypotheses S1982Basis hcycle h

end LeanFormal.IUT.XiFPaper.S2375RangePairTransitiveActual

end
