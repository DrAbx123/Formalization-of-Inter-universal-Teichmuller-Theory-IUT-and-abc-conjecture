import tmp.sheaf.xif.paper.S2229RangeTransitivityActual
import tmp.sheaf.xif.paper.S1987D5LargeImageFiveActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2236GaloisPairTransitiveActual

open LeanFormal.IUT.XiFPaper.S2229RangeTransitivityActual
open LeanFormal.IUT.XiFPaper.S2218RangePairTransitiveActual
open LeanFormal.IUT.XiFPaper.S2203D5RangeActual
open LeanFormal.IUT.XiFPaper.S1987D5LargeImageFiveActual
open LeanFormal.IUT.XiFPaper.S1982D5FiveActual

/-- Exact Galois-transitivity target on the twelve affine pairs. -/
abbrev S2236GaloisTransitivityRequired : Prop :=
  S2229ActualGaloisPairTransitiveRequired

/-- Exact compatibility target between transferred-range transitivity and
the S2203 pair-transitivity hypothesis. -/
abbrev S2236RangeCompatibilityRequired : Prop :=
  S2229TransferredPairCompatibilityRequired

/-- The actual Galois-transitivity target gives transitivity of the
transferred range (S2229 equivalence). -/
theorem S2236TransferredRangeTransitive_of_galois
    (h : S2236GaloisTransitivityRequired) :
    S2218AffinePairTransitive (S2229TransferredRange S1982Basis) :=
  (S2229GaloisPairTransitive_iff S1982Basis).mp h

/-- Conditional assembly of the S2203 range pair-transitivity from the exact
two remaining facts. -/
theorem S2236RangePairTransitive_of_exact
    (h : S2236GaloisTransitivityRequired)
    (hcomp : S2236RangeCompatibilityRequired) :
    S2203RangePairTransitiveRequired S1982Basis :=
  S2229RangePairTransitive_of_transferred
    (S2236TransferredRangeTransitive_of_galois h) hcomp

/-- Conditional D5 assembly. -/
theorem S2236D5LargeImageFive_of_exact
    (h : S2236GaloisTransitivityRequired)
    (hcomp : S2236RangeCompatibilityRequired)
    (hcycle : S2203RangeCycleTypeRequired S1982Basis) :
    S1987D5LargeImageFive :=
  S2203D5LargeImageFive_of_rangeHypotheses S1982Basis hcycle
    (S2236RangePairTransitive_of_exact h hcomp)

/-- Exact first missing conjunction. -/
def S2236ExactFirstMissing : Prop :=
  S2236GaloisTransitivityRequired ∧ S2236RangeCompatibilityRequired

end LeanFormal.IUT.XiFPaper.S2236GaloisPairTransitiveActual

end
