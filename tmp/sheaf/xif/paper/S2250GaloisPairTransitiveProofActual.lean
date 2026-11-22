import tmp.sheaf.xif.paper.S2243RangeCompatibilityActual
import tmp.sheaf.xif.paper.S2236GaloisPairTransitiveActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2250GaloisPairTransitiveProofActual

open LeanFormal.IUT.XiFPaper.S2243RangeCompatibilityActual
open LeanFormal.IUT.XiFPaper.S2236GaloisPairTransitiveActual
open LeanFormal.IUT.XiFPaper.S2229RangeTransitivityActual
open LeanFormal.IUT.XiFPaper.S2218RangePairTransitiveActual
open LeanFormal.IUT.XiFPaper.S2203D5RangeActual
open LeanFormal.IUT.XiFPaper.S1987D5LargeImageFiveActual
open LeanFormal.IUT.XiFPaper.S1982D5FiveActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S2009DicksonActual

/-- Exact Galois transitivity target on the actual twelve affine pairs. -/
abbrev S2250GaloisPairTransitiveRequired : Prop :=
  S2236GaloisTransitivityRequired

/-- The exact target is equivalently transitivity of the actual mod-5 range
on the affine pairs (via S2229 plus the actual transferred-range identity). -/
theorem S2250GaloisPairTransitiveRequired_iff_range :
    S2250GaloisPairTransitiveRequired ↔
      S2218AffinePairTransitive
        (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis).range := by
  unfold S2250GaloisPairTransitiveRequired S2236GaloisTransitivityRequired
  rw [← S2243TransferredRange_eq S1982Basis]
  exact S2229GaloisPairTransitive_iff S1982Basis

/-- Exact first missing: the Galois/range affine-pair transitivity. -/
def S2250ExactFirstMissing : Prop :=
  S2250GaloisPairTransitiveRequired

/-- Conditional D5: exact Galois transitivity plus the actual range cycle
type gives the S1987 target. -/
theorem S2250D5LargeImageFive_of_exact
    (h : S2250ExactFirstMissing)
    (hcycle : S2203RangeCycleTypeRequired S1982Basis) :
    S1987D5LargeImageFive :=
  S2243D5LargeImageFive_of_galois h hcycle

end LeanFormal.IUT.XiFPaper.S2250GaloisPairTransitiveProofActual

end
