import tmp.sheaf.xif.paper.Mzk1ABCTwoEstimatesHeightLemmasShaActual
import tmp.sheaf.xif.paper.Mzk1IUTIVStage5NumericalActual
import Mathlib.Tactic

-- AUDIT A612 WARNING: these are MODEL-form lemmas with logVolume := arithmeticWeight.
-- They do NOT narrow the real paper HeightEstimate (region log-volume, IUT IV sec 2,
-- height_le_normalizedRegionVolume); pointwise height <= arithmeticWeight is false in
-- general (3+125=128). See Mzk1ABCTwoEstimatesAuditCorrectionShaActual for the honest interface.

/-!
# shehdd A611 HeightEstimate substantive lemmas (Sha)

* pointwise height-vs-weight bound over ABC triples ⇒ `height_estimate` shape;
* the `forall δ > 0` estimate implies the single pointwise bound `h <= w`
  (so the height estimate is *equivalent* to the weight bound, not weaker);
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesHeightWeightShaActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1IUTIVStage5ABCFormActual
open LeanFormal.IUT.XiFPaper.Mzk1IUTIVStage5NumericalActual
open LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesHeightLemmasShaActual

theorem height_estimate_of_height_bound_of_triples
    (hheight : ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤ arithmeticWeight (abcRationalPoint a c)) :
    ∀ δ : Real, 0 < δ → ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + δ) * arithmeticWeight (abcRationalPoint a c) := by
  intro δ hδ a b c htriple
  exact height_estimate_of_weight_bound
    (arithmeticWeight_nonneg_local (abcRationalPoint a c)) hδ (hheight a b c htriple)

/-- From the estimate for every `δ > 0` one recovers the pointwise bound `h <= w`
(for `w > 0`). -/
theorem height_le_weight_of_forall_estimate {h w : Real} (hw : 0 < w)
    (H : ∀ δ : Real, 0 < δ → h ≤ (1 + δ) * w) : h ≤ w := by
  by_contra hle
  push_neg at hle
  have hpos : 0 < (h - w) / (2 * w) := div_pos (sub_pos.mpr hle) (by positivity)
  have hstep := H ((h - w) / (2 * w)) hpos
  have hlt : (1 + (h - w) / (2 * w)) * w < h := by
    field_simp
    nlinarith
  linarith

/-- The height estimate (for all `δ > 0`) is equivalent to the pointwise
bound `h <= w` when `w > 0`. -/
theorem height_estimate_iff_weight_bound {h w : Real} (hw : 0 < w) :
    (∀ δ : Real, 0 < δ → h ≤ (1 + δ) * w) ↔ h ≤ w := by
  constructor
  · intro H; exact height_le_weight_of_forall_estimate hw H
  · intro hbound δ hδ
    exact height_estimate_of_weight_bound (le_of_lt hw) hδ hbound

end LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesHeightWeightShaActual
