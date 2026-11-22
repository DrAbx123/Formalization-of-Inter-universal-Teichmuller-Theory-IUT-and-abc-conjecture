import tmp.sheaf.xif.paper.Mzk1ABCTwoEstimatesShaActual
import tmp.sheaf.xif.paper.Mzk1ABCTwoEstimatesHeightLemmasShaActual
import tmp.sheaf.xif.paper.Mzk1IUTIVStage5NumericalActual

/-!
# shehdd A612 AUDIT CORRECTION: real HeightEstimate vs the weight model (Sha)

## Warning
`Mzk1ABCTwoEstimatesHeightWeightShaActual.height_estimate_iff_weight_bound` is a
**MODEL-form** lemma: it is only meaningful when the estimate's `logVolume` is
chosen to be `arithmeticWeight`.  The real paper HeightEstimate uses the paper
**region log-volume** (IUT IV section 2, `height_le_normalizedRegionVolume`, in
hull/abc-owned `Mzk1ABCBridgeHeightRegionActual`), not the arithmetic weight.

Pointwise `Height.logHeight₁ (abcRationalPoint a c) ≤ arithmeticWeight (...)`
is false in general: 3+125=128 gives c=128, rad(128·3)=30, height > weight.
Therefore the weight equivalence must NOT be presented as narrowing the real
HeightEstimate gap.

## Honest gap interface
`RealHeightEstimateInterface` packages the actual paper content: an arbitrary
region log-volume `logVolume` and the pointwise bound
`height ≤ logVolume` (the named IUT IV height-vs-region-volume comparison).
It yields the `height_estimate` slot with the SAME region log-volume.

No sorry, axiom, True or placeholder.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesAuditCorrectionShaActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1IUTIVStage5ABCFormActual
open LeanFormal.IUT.XiFPaper.Mzk1IUTIVStage5NumericalActual
open LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesHeightLemmasShaActual

/-- Honest real HeightEstimate interface: `logVolume` is the paper region
log-volume (arbitrary model-independent input), `height_le_logVolume` is the
named IUT IV height-vs-region-volume content. -/
structure RealHeightEstimateInterface where
  logVolume : Nat → Nat → Nat → Real
  logVolume_nonneg : ∀ a b c : Nat, 0 ≤ logVolume a b c
  height_le_logVolume : ∀ a b c : Nat, IsABCTriple a b c →
    Height.logHeight₁ (abcRationalPoint a c) ≤ logVolume a b c

/-- The honest interface gives the `height_estimate` slot with the SAME region
log-volume (no weight substitution). -/
theorem height_estimate_of_realInterface (R : RealHeightEstimateInterface) :
    ∀ δ : Real, 0 < δ → ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + δ) * R.logVolume a b c := by
  intro δ hδ a b c htriple
  exact height_estimate_of_weight_bound (R.logVolume_nonneg a b c) hδ
    (R.height_le_logVolume a b c htriple)

/-- The actual named content, re-exported: pointwise height vs region volume. -/
theorem real_height_le_regionVolume (R : RealHeightEstimateInterface) :
    ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤ R.logVolume a b c :=
  R.height_le_logVolume

end LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesAuditCorrectionShaActual
