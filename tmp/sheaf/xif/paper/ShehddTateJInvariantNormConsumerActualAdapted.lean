import LeanFormal.IUT.Foundations.Geometry.TateJInvariantNorm

/-!
# ShehddTateJInvariantNormConsumerActualAdapted — Tate j-invariant norm consumer

STEP 0 prior-art (reuse only; A475 search: Tate j norm assets found):
* Foundations/Geometry/TateJInvariantNorm.lean (namespace TateCurvePadic):
  tateJInvariant, tateJInvariant_norm (||j|| = ||q||^-1), _norm_eq_inv_delta_norm,
  _norm_eq_prime (||j|| = l.value), _norm_gt_one, _norm_pos, _norm_mul_q_norm
  (||j|| * ||q|| = 1), _ne_zero, _mul_delta, _not_integral_element.

This file packages the Tate j-invariant norm facts as one consumer for the q-pilot /
Tate-uniformization layer.  No new assumptions, no sorry/axiom.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddTateJInvariantNormConsumerActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.TateCurvePadic

variable (l : PrimeGeFive) [Fact (Nat.Prime l.value)]

/-- **PROVED consumer:** the Tate j-invariant norm is the inverse q norm (= l.value),
strictly greater than one, multiplicative inverse to ||q||, and j satisfies jΔ = c₄³. -/
theorem tateJInvariant_norm_summary :
    ‖tateJInvariant l‖ = (‖q l‖)⁻¹ ∧
      ‖tateJInvariant l‖ = (l.value : ℝ) ∧
        1 < ‖tateJInvariant l‖ ∧
          ‖tateJInvariant l‖ * ‖q l‖ = 1 ∧
            tateJInvariant l * (canonicalCurve l).Δ = (canonicalCurve l).c₄ ^ 3 :=
  ⟨tateJInvariant_norm l, tateJInvariant_norm_eq_prime l,
    tateJInvariant_norm_gt_one l, tateJInvariant_norm_mul_q_norm l,
    tateJInvariant_mul_delta l⟩

/-- **PROVED consumer:** the j-invariant is nonzero and its norm positive. -/
theorem tateJInvariant_norm_pos_and_ne_zero :
    tateJInvariant l ≠ 0 ∧ 0 < ‖tateJInvariant l‖ :=
  ⟨tateJInvariant_ne_zero l, tateJInvariant_norm_pos l⟩

/-- Row record: reused Tate j norm assets vs the consumer interface. -/
def tateJInvariantNormRows : List (String × String × String) :=
  [ ("exact norm ||j|| = ||q||^-1 = l.value", "REUSED PROVED", "TateJInvariantNorm.tateJInvariant_norm / _norm_eq_prime")
  , ("||j|| > 1 and positive; ||j||*||q|| = 1", "REUSED PROVED", "_norm_gt_one / _norm_pos / _norm_mul_q_norm")
  , ("j nonzero; j*Delta = c4^3", "REUSED PROVED", "_ne_zero / _mul_delta")
  , ("consumer bundle", "COMPOSED PROVED", "tateJInvariant_norm_summary, tateJInvariant_norm_pos_and_ne_zero")
  , ("non-integrality of j (not in image of integral elements)", "REUSED PROVED", "tateJInvariant_not_integral_element") ]

theorem tateJInvariantNormRows_length : tateJInvariantNormRows.length = 5 := rfl

#check tateJInvariant_norm_summary
#check tateJInvariant_norm_pos_and_ne_zero
#check tateJInvariantNormRows_length

end LeanFormal.IUT.XiFPaper.ShehddTateJInvariantNormConsumerActualAdapted
end
