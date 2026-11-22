import tmp.sheaf.xif.paper.Mzk1ABCTwoEstimatesShaActual
import tmp.sheaf.xif.paper.Mzk1ABCTwoEstimatesHeightLemmasShaActual
import tmp.sheaf.xif.paper.Mzk1ABCTwoEstimatesVolumeLemmasShaActual
import tmp.sheaf.xif.paper.Mzk1IUTIVStage5NumericalActual

/-!
# A596 two-estimates reduction interface (shehdd)

Integrates the reduction interfaces for the two IUT IV Thm 1.10 estimates:
* height side: a pointwise `Height.logHeight <= logVolume` bound (with
  nonnegative logVolume) gives the `height_estimate` slot;
* volume side: a pointwise additive bound gives the `volume_estimate` slot.

Thus the two named estimates reduce to one pointwise height bound plus one
pointwise additive volume bound; `ABCConjecture` follows through the green
`abc_of_twoEstimates`.  The `ABCTwoEstimates` object is not changed.

No sorry, axiom, True or placeholder.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesReductionShaActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1IUTIVStage5ABCFormActual
open LeanFormal.IUT.XiFPaper.Mzk1IUTIVStage5NumericalActual
open LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesShaActual
open LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesHeightLemmasShaActual
open LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesVolumeLemmasShaActual

structure ABCTwoEstimatesReductions where
  logVolume : Nat → Nat → Nat → Real
  logVolume_nonneg : ∀ a b c : Nat, 0 ≤ logVolume a b c
  hullVolume : Real
  D0 : Real
  height_pointwise : ∀ a b c : Nat, IsABCTriple a b c →
    Height.logHeight₁ (abcRationalPoint a c) ≤ logVolume a b c
  volume_additive : ∀ a b c : Nat, IsABCTriple a b c →
    logVolume a b c ≤ arithmeticWeight (abcRationalPoint a c) + hullVolume + D0

noncomputable def toABCTwoEstimates (R : ABCTwoEstimatesReductions) : ABCTwoEstimates where
  logVolume := R.logVolume
  hullVolume := R.hullVolume
  height_estimate := by
    intro δ hδ a b c htriple
    exact height_estimate_of_weight_bound (R.logVolume_nonneg a b c) hδ
      (R.height_pointwise a b c htriple)
  volume_estimate := volume_estimate_of_additive_bound_of_triples R.volume_additive

theorem abc_of_reductions (R : ABCTwoEstimatesReductions) : ABCConjecture :=
  abc_of_twoEstimates (toABCTwoEstimates R)

/-- Thin re-export: the height-bound form of the reduction. -/
theorem abc_of_reductions_heightBound (R : ABCTwoEstimatesReductions) :
    ABCFormAdditiveHeightBound :=
  heightBound_of_twoEstimates (toABCTwoEstimates R)

end LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesReductionShaActual
