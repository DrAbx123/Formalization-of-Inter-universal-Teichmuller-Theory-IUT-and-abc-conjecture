import tmp.sheaf.xif.paper.Mzk1IUTIVStage5NumericalActual
import Mathlib.Tactic

/-!
# A590 ABC two-estimate gaps (shehdd formalization)

The two named literal log-volume estimates of IUT IV Stage 5 as an explicit
structure, plus the consumer theorem that they imply `ABCConjecture` via the
green numerical reduction.  This is formalization of the gap shape, not a claim
that the estimates are proved.

No sorry, axiom, True or placeholder.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesShaActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1IUTIVStage5ABCFormActual
open LeanFormal.IUT.XiFPaper.Mzk1IUTIVStage5NumericalActual

structure ABCTwoEstimates where
  logVolume : Nat → Nat → Nat → Real
  hullVolume : Real
  height_estimate : ∀ δ : Real, 0 < δ → ∀ a b c : Nat, IsABCTriple a b c →
    Height.logHeight₁ (abcRationalPoint a c) ≤ (1 + δ) * logVolume a b c
  volume_estimate : ∀ δ : Real, 0 < δ → ∃ D : Real,
    ∀ a b c : Nat, IsABCTriple a b c →
      logVolume a b c ≤ (1 + δ) * arithmeticWeight (abcRationalPoint a c) +
        hullVolume + D

theorem abc_of_twoEstimates (E : ABCTwoEstimates) : ABCConjecture :=
  abcConjecture_of_literalLogVolumeEstimates E.logVolume E.hullVolume
    E.height_estimate E.volume_estimate

theorem heightBound_of_twoEstimates (E : ABCTwoEstimates) :
    ABCFormAdditiveHeightBound :=
  additiveHeightBound_of_literalLogVolumeEstimates E.logVolume E.hullVolume
    E.height_estimate E.volume_estimate

end LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesShaActual
