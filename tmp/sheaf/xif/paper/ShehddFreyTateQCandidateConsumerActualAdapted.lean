import LeanFormal.IUT.ABCBridge.Geometry.FreyTateAnalyticInput
import LeanFormal.IUT.ABCBridge.Geometry.FreyTateParameterComparison

/-!
# ShehddFreyTateQCandidateConsumerActualAdapted — Frey/Tate q-parameter analytic consumer

STEP 0 prior-art (reuse only; A475 search: FreyTate q assets found):
* FreyTateAnalyticInput.lean: freyAbcTateCandidateQ (_def, _ne_zero, _norm_lt_one,
  _ne_one, _pow_norm_lt_one, _norm_le_invNine, _lambertSeries_summable,
  _arithmeticCertificate);
* FreyTateParameterComparison.lean: freyAbcJInvariantAtP,
  freyAbcTateCandidateQ_eq_inv_freyAbcJInvariantAtP,
  freyAbcTateCandidateQ_norm_eq_inv_freyAbcJInvariantAtP_norm.

This file packages the Frey Tate-parameter candidate's analytic facts as one consumer for
the q-pilot / Tate-uniformization layer: nonzero, strictly contracting (<1 and <= 1/9),
non-one, the arithmetic certificate, and the identification with j^-1.  No new
assumptions, no sorry/axiom.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddFreyTateQCandidateConsumerActualAdapted

open LeanFormal.IUT

variable {a b c p : ℕ} [Fact p.Prime]

/-- **PROVED consumer:** the Frey Tate candidate q := j^-1 is nonzero, strictly
contracting, bounded by 1/9, and identifies with the inverse j-invariant at p. -/
theorem freyTate_candidate_summary (h : IsABCTriple a b c) (hp_two : p ≠ 2)
    (hdiv : p ∣ a * b * c) :
    freyAbcTateCandidateQ p a b c ≠ 0 ∧
      ‖freyAbcTateCandidateQ p a b c‖ < 1 ∧
        ‖freyAbcTateCandidateQ p a b c‖ ≤ (1 / 9 : ℝ) ∧
          freyAbcTateCandidateQ p a b c = (freyAbcJInvariantAtP a b c p h)⁻¹ :=
  ⟨freyAbcTateCandidateQ_ne_zero h hp_two hdiv,
    freyAbcTateCandidateQ_norm_lt_one h hp_two hdiv,
    freyAbcTateCandidateQ_norm_le_invNine h hp_two hdiv,
    freyAbcTateCandidateQ_eq_inv_freyAbcJInvariantAtP a b c p h⟩

/-- **PROVED consumer:** the candidate's norm is the inverse norm of the p-adic Frey
j-invariant. -/
theorem freyTate_candidate_norm_summary (h : IsABCTriple a b c) (hp_two : p ≠ 2)
    (hdiv : p ∣ a * b * c) :
    freyAbcTateCandidateQ p a b c ≠ 1 ∧
      ‖freyAbcTateCandidateQ p a b c‖ = (‖freyAbcJInvariantAtP a b c p h‖)⁻¹ :=
  ⟨freyAbcTateCandidateQ_ne_one h hp_two hdiv,
    freyAbcTateCandidateQ_norm_eq_inv_freyAbcJInvariantAtP_norm a b c p h⟩

/-- **PROVED consumer:** the candidate carries the Tate arithmetic certificate. -/
theorem freyTate_candidate_arithmeticCertificate (h : IsABCTriple a b c)
    (hp_two : p ≠ 2) (hdiv : p ∣ a * b * c) :
    TateCurve.ArithmeticCertificate (freyAbcTateCandidateQ p a b c) :=
  freyAbcTateCandidateQ_arithmeticCertificate h hp_two hdiv

/-- Row record: reused Frey/Tate analytic assets vs the consumer interface. -/
def freyTateCandidateRows : List (String × String × String) :=
  [ ("candidate nonzero / norm<1 / <=1/9", "REUSED PROVED", "FreyTateAnalyticInput.freyAbcTateCandidateQ_ne_zero/_norm_lt_one/_norm_le_invNine")
  , ("candidate = j^-1 and norm = ||j||^-1", "REUSED PROVED", "FreyTateParameterComparison.freyAbcTateCandidateQ_eq_inv_freyAbcJInvariantAtP(_norm)")
  , ("candidate arithmetic certificate (Tate uniformization input)", "REUSED PROVED", "FreyTateAnalyticInput.freyAbcTateCandidateQ_arithmeticCertificate")
  , ("candidate consumer summaries", "COMPOSED PROVED", "freyTate_candidate_summary, freyTate_candidate_norm_summary, freyTate_candidate_arithmeticCertificate")
  , ("power/1-q^n/Lambert-series properties", "REUSED PROVED (available, not restated here)", "freyAbcTateCandidateQ_pow_norm_lt_one/_one_sub_pow_ne_zero/_lambertSeries_summable") ]

theorem freyTateCandidateRows_length : freyTateCandidateRows.length = 5 := rfl

#check freyTate_candidate_summary
#check freyTate_candidate_norm_summary
#check freyTate_candidate_arithmeticCertificate
#check freyTateCandidateRows_length

end LeanFormal.IUT.XiFPaper.ShehddFreyTateQCandidateConsumerActualAdapted
end
