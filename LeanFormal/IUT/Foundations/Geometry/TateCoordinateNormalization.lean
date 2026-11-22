import LeanFormal.IUT.Foundations.Geometry.TateWeierstrassPointEquation

/-!
# Constant normalization of the Tate coordinates

The existing `tateWeierstrassX` and `tateWeierstrassY` are the raw bilateral
kernel sums. The coordinates for the canonical Tate equation are instead
`X = rawX - 2 s` and `Y = rawY + s`, with
`s = sum_{n >= 1} q^n / (1 - q^n)^2`.

Reference: Silverman, Advanced Topics, p.425; the formulas are also implemented
by Sage's `parametrisation_onto_tate_curve` in `ell_tate_curve.py`.

This file proves the exact coordinate change and its effect on the polynomial
equation. It does not assume or prove the analytic Tate equation. In particular,
the old raw-coordinate equation is not used as the missing analytic input.
-/

namespace LeanFormal.IUT.TateCurve

noncomputable section

/-- The constant subtracted twice from the raw X-series and added to the raw Y-series. -/
def tateCoordinateCorrection {K : Type*} [NormedField K] (q : K) : K :=
  ∑' n : ℕ, coordinateKernel (q ^ (n + 1))

/-- The correction is a convergent series under the usual Tate norm hypothesis. -/
theorem summable_tateCoordinateCorrection
    {K : Type*} [NormedField K] [CompleteSpace K] {q : K}
    (parameterNorm : ‖q‖ < 1) :
    Summable (fun n : ℕ ↦ coordinateKernel (q ^ (n + 1))) := by
  have all_indices := coordinateKernel_int_summable parameterNorm (1 : K)
  have positive_indices := all_indices.comp_injective
    (i := fun n : ℕ ↦ ((n + 1 : ℕ) : ℤ)) (by
      intro first second equality
      change ((first + 1 : ℕ) : ℤ) = ((second + 1 : ℕ) : ℤ) at equality
      exact Nat.add_right_cancel (Int.ofNat_inj.mp equality))
  simpa only [Function.comp_def, zpow_natCast, mul_one] using positive_indices

/-- The normalized X-coordinate for the canonical Tate Weierstrass equation. -/
def normalizedTateX {K : Type*} [NormedField K] (q u : K) : K :=
  tateWeierstrassX q u - 2 * tateCoordinateCorrection q

/-- The normalized Y-coordinate for the canonical Tate Weierstrass equation. -/
def normalizedTateY {K : Type*} [NormedField K] (q u : K) : K :=
  tateWeierstrassY q u + tateCoordinateCorrection q

theorem normalizedTateX_zpow_mul_parameter
    {K : Type*} [NormedField K] {q : K} (parameterNeZero : q ≠ 0) (m : ℤ) (u : K) :
    normalizedTateX q (q ^ m * u) = normalizedTateX q u := by
  simp only [normalizedTateX, tateWeierstrassX_zpow_mul_parameter parameterNeZero]

theorem normalizedTateY_zpow_mul_parameter
    {K : Type*} [NormedField K] {q : K} (parameterNeZero : q ≠ 0) (m : ℤ) (u : K) :
    normalizedTateY q (q ^ m * u) = normalizedTateY q u := by
  simp only [normalizedTateY, tateWeierstrassY_zpow_mul_parameter parameterNeZero]

/-- The odd coordinate is unchanged by the constant normalization. -/
theorem two_mul_normalizedTateY_add_normalizedTateX
    {K : Type*} [NormedField K] [CompleteSpace K] {q : K}
    (parameterNorm : ‖q‖ < 1) (u : K) :
    2 * normalizedTateY q u + normalizedTateX q u = inversionOddYCoordinateSeries q u := by
  have raw_relation := two_mul_tateWeierstrassY_eq_oddSeries_sub_X parameterNorm u
  unfold normalizedTateX normalizedTateY
  linear_combination raw_relation

/-- The exact residual introduced by omitting the Tate coordinate constants. -/
theorem tate_coordinate_shift_residual
    {R : Type*} [CommRing R] (rawX rawY correction coefficient4 coefficient6 : R) :
    (rawY + correction) ^ 2 + (rawX - 2 * correction) * (rawY + correction) -
        ((rawX - 2 * correction) ^ 3 + coefficient4 * (rawX - 2 * correction) + coefficient6) =
      (rawY ^ 2 + rawX * rawY - (rawX ^ 3 + coefficient4 * rawX + coefficient6)) +
        correction * (6 * rawX ^ 2 + (1 - 12 * correction) * rawX +
          8 * correction ^ 2 - correction + 2 * coefficient4) := by
  ring

/-- The canonical equation on normalized coordinates is a different polynomial
equation on the raw coordinates. This equivalence supplies no analytic identity. -/
theorem normalizedTate_equation_iff_raw_shifted_coefficients
    {K : Type*} [NormedField K] [CharZero K] (q u : K) :
    (weierstrassCurve K q).toAffine.Equation (normalizedTateX q u) (normalizedTateY q u) ↔
      tateWeierstrassY q u ^ 2 + tateWeierstrassX q u * tateWeierstrassY q u =
        tateWeierstrassX q u ^ 3 -
          6 * tateCoordinateCorrection q * tateWeierstrassX q u ^ 2 +
          (a4 K q - tateCoordinateCorrection q + 12 * tateCoordinateCorrection q ^ 2) *
            tateWeierstrassX q u +
          (a6 K q - 2 * a4 K q * tateCoordinateCorrection q +
            tateCoordinateCorrection q ^ 2 - 8 * tateCoordinateCorrection q ^ 3) := by
  rw [WeierstrassCurve.Affine.equation_iff, tateCanonicalAffine_a₁,
    tateCanonicalAffine_a₂, tateCanonicalAffine_a₃, tateCanonicalAffine_a₄, tateCanonicalAffine_a₆]
  simp only [one_mul, zero_mul, add_zero, normalizedTateX, normalizedTateY]
  constructor <;> intro equation <;> linear_combination equation

/-- The corrected analytic target in odd-coordinate form; the identity itself
still requires proof. Its X-coordinate includes the constant correction. -/
theorem normalizedTate_equation_iff_oddSeries
    {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K] {q : K}
    (parameterNorm : ‖q‖ < 1) (u : K) :
    (weierstrassCurve K q).toAffine.Equation (normalizedTateX q u) (normalizedTateY q u) ↔
      inversionOddYCoordinateSeries q u ^ 2 =
        4 * normalizedTateX q u ^ 3 + normalizedTateX q u ^ 2 +
          4 * a4 K q * normalizedTateX q u + 4 * a6 K q := by
  rw [WeierstrassCurve.Affine.equation_iff, tateCanonicalAffine_a₁,
    tateCanonicalAffine_a₂, tateCanonicalAffine_a₃, tateCanonicalAffine_a₄, tateCanonicalAffine_a₆]
  simp only [one_mul, zero_mul, add_zero]
  rw [← two_mul_normalizedTateY_add_normalizedTateX parameterNorm u]
  constructor
  · intro equation
    linear_combination 4 * equation
  · intro odd_equation
    linear_combination (1 / 4 : K) * odd_equation

end

end LeanFormal.IUT.TateCurve
