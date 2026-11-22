import tmp.sheaf.xif.paper.Mzk1ABCTwoEstimatesHeightLemmasShaActual
import tmp.sheaf.xif.paper.Mzk1ABCTwoEstimatesHeightWeightShaActual
import tmp.sheaf.xif.paper.Mzk1IUTIVStage5NumericalActual

/-!
# shehdd A631 Gap1/Gap2 substantive limit lemmas (Sha)

Honest quantitative reductions:
* Gap1 ε-form with a **positive region log-volume** implies the pointwise comparison
  `height ≤ regionVolume` (same region volume, no weight substitution);
* Gap2 ε-form with a **uniform** `D` (same D for every ε) implies the pointwise
  additive bound with the same `D`.

These are real implications (not equivalences in the weak ε-form with D(ε)); the
named Gap1/Gap2 inputs themselves remain named.

No sorry, axiom, True or placeholder.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesGapLimitShaActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1IUTIVStage5ABCFormActual
open LeanFormal.IUT.XiFPaper.Mzk1IUTIVStage5NumericalActual
open LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesHeightLemmasShaActual
open LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesHeightWeightShaActual

/-- Gap1 limit: `∀ε>0, h ≤ (1+ε)L` with `L > 0` implies `h ≤ L`. -/
theorem height_le_regionVolume_of_epsilon {h L : Real} (hL : 0 < L)
    (H : ∀ ε : Real, 0 < ε → h ≤ (1 + ε) * L) : h ≤ L :=
  height_le_weight_of_forall_estimate hL H

/-- Pointwise Gap1 form: the ε-normalized height comparison with a positive region
log-volume implies `height ≤ regionVolume` (same region volume). -/
theorem gap1_pointwise_of_epsilon
    (regionVolume : Nat → Nat → Nat → Real)
    (hpos : ∀ a b c : Nat, IsABCTriple a b c → 0 < regionVolume a b c)
    (H : ∀ ε : Real, 0 < ε → ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤ (1 + ε) * regionVolume a b c) :
    ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤ regionVolume a b c := by
  intro a b c htriple
  exact height_le_regionVolume_of_epsilon (hpos a b c htriple)
    (fun ε hε => H ε hε a b c htriple)

/-- Gap2 limit: a uniform `D` in `∀ε>0, v ≤ (1+ε)w + hull + D` implies the
pointwise additive bound with the same `D` (for `w > 0`). -/
theorem volume_additive_of_uniform_epsilon {v w hull D : Real} (hw : 0 < w)
    (H : ∀ ε : Real, 0 < ε → v ≤ (1 + ε) * w + hull + D) :
    v ≤ w + hull + D := by
  by_contra hle
  push_neg at hle
  have hpos : 0 < (v - (w + hull + D)) / (2 * w) := div_pos (sub_pos.mpr hle) (by positivity)
  have hstep := H _ hpos
  have hlt : (1 + (v - (w + hull + D)) / (2 * w)) * w + hull + D < v := by
    field_simp
    nlinarith
  linarith

/-- Gap2 with a single uniform constant D over all eps and triples gives the
pointwise additive bound with the SAME D, provided the weights are positive at
ABC triples. -/
theorem gap2_pointwise_of_uniform
    (regionVolume weight hull : Nat → Nat → Nat → Real)
    (H : ∃ D : Real, ∀ ε : Real, 0 < ε → ∀ a b c : Nat, IsABCTriple a b c →
      regionVolume a b c ≤ (1 + ε) * weight a b c + hull a b c + D)
    (hweight : ∀ a b c : Nat, IsABCTriple a b c → 0 < weight a b c) :
    ∃ D : Real, ∀ a b c : Nat, IsABCTriple a b c →
      regionVolume a b c ≤ weight a b c + hull a b c + D := by
  obtain ⟨D, hD⟩ := H
  exact ⟨D, fun a b c htriple =>
    volume_additive_of_uniform_epsilon (hweight a b c htriple)
      (fun ε hε => hD ε hε a b c htriple)⟩

/-- Gap1 ε-form is EQUIVALENT to the pointwise region-volume comparison when the
region log-volume is positive. -/
theorem gap1_epsilon_iff_pointwise {h L : Real} (hL : 0 < L) :
    (∀ eps : Real, 0 < eps → h ≤ (1 + eps) * L) ↔ h ≤ L := by
  constructor
  · intro H; exact height_le_regionVolume_of_epsilon hL H
  · intro hbound eps heps
    have hmono : (1 + 0) * L ≤ (1 + eps) * L := by
      apply mul_le_mul_of_nonneg_right _ (le_of_lt hL); linarith
    linarith

/-- Gap2 with a uniform D: the ε-form is EQUIVALENT to the pointwise additive
bound with the same D (for positive weight). -/
theorem gap2_uniform_iff_pointwise {v w hull D : Real} (hw : 0 < w) :
    (∀ eps : Real, 0 < eps → v ≤ (1 + eps) * w + hull + D) ↔
      v ≤ w + hull + D := by
  constructor
  · intro H; exact volume_additive_of_uniform_epsilon hw H
  · intro hbound eps heps
    have hweps : 0 ≤ eps * w := mul_nonneg (le_of_lt heps) (le_of_lt hw)
    linarith
end LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesGapLimitShaActual
