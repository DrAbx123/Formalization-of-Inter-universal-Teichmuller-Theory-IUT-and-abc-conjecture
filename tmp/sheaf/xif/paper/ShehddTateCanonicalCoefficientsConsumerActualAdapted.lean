import LeanFormal.IUT.Foundations.Geometry.TateCurveArithmetic

/-!
# ShehddTateCanonicalCoefficientsConsumerActualAdapted — Tate canonical equation consumer

STEP 0 prior-art (reuse only; A475 search: Tate q-series coefficients found):
* Foundations/Geometry/TateCurveArithmetic.lean (namespace TateCurve): canonical_a₁..a₆,
  canonical_equation_coefficients, canonical_b₂/b₄/b₆/b₈, canonical_b_relation,
  canonical_c₄/c₆, canonical_delta(+_expanded_in_series), canonical_c_relation,
  canonical_c₄_sub_one, canonical_c₆_add_one, canonical_delta_as_b₈_correction,
  canonical_delta_eq_zero_iff, canonical_delta_ne_zero_iff.

This file packages the Tate canonical equation coefficients and Weierstrass relations as
one consumer for the q-series curve model (IUT I, Definition 3.1(b)-(c) arithmetic part).
No new assumptions, no sorry/axiom.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddTateCanonicalCoefficientsConsumerActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.TateCurve

universe u

variable {K : Type u} [NormedField K] [CharZero K]

/-- **PROVED consumer:** the canonical coefficients and invariants of the Tate curve.
-/
theorem tateCanonical_consumer (q : K) :
    ((weierstrassCurve K q).a₁, (weierstrassCurve K q).a₂,
        (weierstrassCurve K q).a₃, (weierstrassCurve K q).a₄,
        (weierstrassCurve K q).a₆) = (1, 0, 0, a4 K q, a6 K q) ∧
      (weierstrassCurve K q).b₂ = 1 ∧
        (weierstrassCurve K q).c₄ = 1 - 48 * a4 K q ∧
          (weierstrassCurve K q).Δ =
            (a4 K q) ^ 2 - a6 K q - 64 * (a4 K q) ^ 3 -
              432 * (a6 K q) ^ 2 + 72 * a4 K q * a6 K q :=
  ⟨TateCurve.canonical_equation_coefficients q,
    TateCurve.canonical_b₂ q,
    TateCurve.canonical_c₄ q,
    TateCurve.canonical_delta q⟩

/-- **PROVED consumer:** the two Weierstrass relations (b-relation and c-relation). -/
theorem tateCanonical_relations_consumer (q : K) :
    4 * (weierstrassCurve K q).b₈ =
        (weierstrassCurve K q).b₂ * (weierstrassCurve K q).b₆ -
          (weierstrassCurve K q).b₄ ^ 2 ∧
      1728 * (weierstrassCurve K q).Δ =
        (weierstrassCurve K q).c₄ ^ 3 - (weierstrassCurve K q).c₆ ^ 2 :=
  ⟨TateCurve.canonical_b_relation q, TateCurve.canonical_c_relation q⟩

/-- Row record: reused Tate-coefficient laws vs the consumer bundles. -/
def tateCanonicalRows : List (String × String × String) :=
  [ ("coefficients a1..a6", "REUSED PROVED", "canonical_a₁..a₆ / canonical_equation_coefficients")
  , ("b-invariants and b-relation", "REUSED PROVED", "canonical_b₂/b₄/b₆/b₈ / canonical_b_relation")
  , ("c-invariants, delta and c-relation", "REUSED PROVED", "canonical_c₄/c₆ / canonical_delta / canonical_c_relation")
  , ("delta zero/nonzero criteria and b8 correction form", "REUSED PROVED", "canonical_delta_eq_zero_iff / _ne_zero_iff / _as_b₈_correction")
  , ("consumer bundles", "COMPOSED PROVED", "tateCanonical_consumer, tateCanonical_relations_consumer") ]

theorem tateCanonicalRows_length : tateCanonicalRows.length = 5 := rfl

#check tateCanonical_consumer
#check tateCanonical_relations_consumer
#check tateCanonicalRows_length

end LeanFormal.IUT.XiFPaper.ShehddTateCanonicalCoefficientsConsumerActualAdapted
end
