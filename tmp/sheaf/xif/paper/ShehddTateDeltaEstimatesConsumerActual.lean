import LeanFormal.IUT.Foundations.Geometry.TateCurveDiscriminantEstimates

/-!
# ShehddTateDeltaEstimatesConsumerActual — Tate discriminant decomposition consumer

STEP 0 prior-art (reuse only; A475 search: Tate discriminant estimates found):
* Foundations/Geometry/TateCurveDiscriminantEstimates.lean (namespace TateCurvePadic):
  deltaValue and its decomposition terms (deltaSquareTerm, deltaA4CubeTerm,
  deltaA6SquareTerm, deltaMixedTerm, deltaCorrection, deltaLeadingTerm),
  deltaCorrection_expanded, deltaValue_expanded,
  deltaValue_as_leading_plus_correction, deltaValue_as_canonical_series,
  constant norm bounds and q-norm comparison laws.

This file packages the discriminant decomposition and constant norm estimates as one
consumer for the Tate q-series / q-pilot comparison.  No new assumptions, no sorry/axiom.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddTateDeltaEstimatesConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.TateCurvePadic

variable (l : PrimeGeFive) [Fact (Nat.Prime l.value)]

/-- **PROVED consumer:** the Tate discriminant decomposes into its five terms and into
leading term plus correction. -/
theorem deltaValue_decomposition_consumer :
    deltaValue l =
        deltaSquareTerm l - a6Value l + deltaA4CubeTerm l +
          deltaA6SquareTerm l + deltaMixedTerm l ∧
      deltaValue l = deltaLeadingTerm l + deltaCorrection l :=
  ⟨TateCurvePadic.deltaValue_expanded l,
    TateCurvePadic.deltaValue_as_leading_plus_correction l⟩

/-- **PROVED consumer:** the canonical series form of the Tate discriminant. -/
theorem deltaValue_series_consumer :
    deltaValue l =
      (TateCurve.a4 ℚ_[l.value] (q l)) ^ 2 -
        TateCurve.a6 ℚ_[l.value] (q l) -
          64 * (TateCurve.a4 ℚ_[l.value] (q l)) ^ 3 -
            432 * (TateCurve.a6 ℚ_[l.value] (q l)) ^ 2 +
              72 * TateCurve.a4 ℚ_[l.value] (q l) *
                TateCurve.a6 ℚ_[l.value] (q l) :=
  TateCurvePadic.deltaValue_as_canonical_series l

/-- **PROVED consumer:** the constant norm bounds and the q-norm cube comparison. -/
theorem deltaValue_constant_bounds_consumer :
    ‖(64 : ℚ_[l.value])‖ ≤ 1 ∧ ‖(432 : ℚ_[l.value])‖ ≤ 1 ∧
      ‖(72 : ℚ_[l.value])‖ ≤ 1 ∧ ‖q l‖ ^ 3 < ‖q l‖ :=
  ⟨TateCurvePadic.norm_sixty_four_le_one l,
    TateCurvePadic.norm_four_hundred_thirty_two_le_one l,
    TateCurvePadic.norm_seventy_two_le_one l,
    TateCurvePadic.q_norm_cube_lt_q_norm l⟩

/-- Row record: reused discriminant-estimate assets vs the consumer bundles. -/
def tateDeltaRows : List (String × String × String) :=
  [ ("delta decomposition terms + correction", "REUSED DEF/PROVED", "deltaValue_expanded / deltaCorrection_expanded / _as_leading_plus_correction")
  , ("canonical series form", "REUSED PROVED", "deltaValue_as_canonical_series")
  , ("constant p-adic norm bounds", "REUSED PROVED", "norm_64/432/72_le_one + nonneg + five-sq/cube")
  , ("q-norm comparison laws", "REUSED PROVED", "q_norm_cube_lt_q_norm / q_norm_square_nonneg / q_norm_cube_nonneg")
  , ("consumer bundles", "COMPOSED PROVED", "deltaValue_decomposition_consumer, deltaValue_series_consumer, deltaValue_constant_bounds_consumer") ]

theorem tateDeltaRows_length : tateDeltaRows.length = 5 := rfl

#check deltaValue_decomposition_consumer
#check deltaValue_series_consumer
#check deltaValue_constant_bounds_consumer
#check tateDeltaRows_length

end LeanFormal.IUT.XiFPaper.ShehddTateDeltaEstimatesConsumerActual
end
