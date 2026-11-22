/-
  The Weierstrass point equation of the Tate coordinate series pair.

  NORMALIZATION ERRATUM (2026-10-18).
  The definitions below deliberately retain the raw bilateral sums. They are NOT
  the coordinates in the canonical Tate equation: those are rawX - 2*s(q) and
  rawY + s(q), where s(q) = sum_{n>=1} q^n/(1-q^n)^2. Consequently the historical
  description below of the missing raw-coordinate equation as the classical
  analytic identity is inaccurate. All proved equivalences below remain valid,
  but do not use `tateWeierstrassEquation` as the canonical Tate analytic target.
  `TateCoordinateNormalization.lean` supplies the corrected coordinates,
  convergence, periodicity, unchanged odd coordinate, and exact equation shift.
  Its corrected analytic equation is still unproved. No declaration below has
  been redefined by this erratum.

  `TateCoordinateSeries` proved the `x`-series `coordinateSeries q u` with kernel
  `z ↦ z/(1-z)^2`; `TateYCoordinateSeries` proved the `y`-series `yCoordinateSeries q u`
  with kernel `z ↦ z^2/(1-z)^3`, together with the inversion-antisymmetric series
  `inversionOddYCoordinateSeries`; `TateCoordinatePeriodicity` proved the `ℤ`-period of
  all three series and their inversion laws.

  This file fixes the candidate Weierstrass point pair of the Tate/theta parametrisation

      X(q,u) = coordinateSeries q u,      Y(q,u) = yCoordinateSeries q u

  and carries out two things.

  * It proves the exact relation between the y-kernels, hence between the three series:
    the inversion-antisymmetric (odd) series is `2 * Y + X`.  Therefore the odd
    coordinate `O = 2Y + X` of the pair is the already-proved
    `inversionOddYCoordinateSeries`, and the affine Weierstrass equation of the
    canonical `q`-series curve `TateCurve.weierstrassCurve`,

        Y^2 + X*Y = X^3 + a4 q * X + a6 q,

    is *equivalent* to the classical odd-coordinate form

        O^2 = 4 X^3 + X^2 + 4 * a4 q * X + 4 * a6 q.

    The equivalence is proved here; it is the exact strength at which the classical
    theta/sigma identity enters.

  * The odd-coordinate identity itself is an analytic theta identity.  It is **not**
    derivable from the series and periodicity results available here, so it is not
    assumed as an unproved principle and not hidden in a structure field: it is recorded
    as the explicit named hypothesis `tateWeierstrassEquation`, whose relation to the
    canonical coefficients of `TateCurve.weierstrassCurve`, to the odd coordinate, to
    `ℤ`-period, and to Mathlib's `Nonsingular` predicate is then proved.

  What is proved unconditionally below: the kernel identity, the series identity
  `O = 2Y + X`, `ℤ`-periodicity of both coordinates and of the equation, the exact
  coefficient form of the equation, and the decomposition of `Nonsingular` into the
  equation plus non-vanishing of the two partial derivatives.  What remains a
  hypothesis: `tateWeierstrassEquation`, i.e. the classical analytic input.
-/

import LeanFormal.IUT.Foundations.Geometry.TateCoordinatePeriodicity
import LeanFormal.IUT.Foundations.Geometry.TateCurve
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Tactic

namespace LeanFormal.IUT.TateCurve

noncomputable section

open WeierstrassCurve

/-! ## The kernel and series relation between the two y-kernels -/

/-- The inversion-antisymmetric `y`-kernel is twice the raw `y`-kernel plus the
`x`-kernel.  This is the kernel-level content of the classical identity `O = 2y + x`
between the odd Tate coordinate and the two Laurent kernels.  It holds for every `z`:
at `z = 1` both sides totalise to `0`. -/
theorem inversionOddYCoordinateKernel_eq_two_mul_yCoordinateKernel_add_coordinateKernel
    {K : Type*} [Field K] (z : K) :
    inversionOddYCoordinateKernel z = 2 * yCoordinateKernel z + coordinateKernel z := by
  by_cases hden : (1 : K) - z = 0
  · have hz : z = 1 := (sub_eq_zero.mp hden).symm
    rw [hz]
    simp [inversionOddYCoordinateKernel, yCoordinateKernel, coordinateKernel]
  · unfold inversionOddYCoordinateKernel yCoordinateKernel coordinateKernel
    field_simp
    ring

/-- Series form of the kernel identity: the inversion-antisymmetric `y`-series is twice
the raw `y`-series plus the `x`-series.  This uses the unconditional summability of both
integer-indexed series proved in `TateCoordinateSeries` and `TateYCoordinateSeries`;
nothing else is assumed. -/
theorem inversionOddYCoordinateSeries_eq_two_mul_yCoordinateSeries_add_coordinateSeries
    {K : Type*} [NormedField K] [CompleteSpace K] {q : K}
    (parameterNorm : ‖q‖ < 1) (u : K) :
    inversionOddYCoordinateSeries q u = 2 * yCoordinateSeries q u + coordinateSeries q u := by
  have hy : HasSum (fun n : ℤ => yCoordinateKernel (q ^ n * u)) (yCoordinateSeries q u) :=
    (yCoordinateKernel_int_summable parameterNorm u).hasSum
  have hc : HasSum (fun n : ℤ => coordinateKernel (q ^ n * u)) (coordinateSeries q u) :=
    (coordinateKernel_int_summable parameterNorm u).hasSum
  have hodd :
      HasSum (fun n : ℤ => inversionOddYCoordinateKernel (q ^ n * u))
        (2 * yCoordinateSeries q u + coordinateSeries q u) := by
    simpa only [inversionOddYCoordinateKernel_eq_two_mul_yCoordinateKernel_add_coordinateKernel]
      using (hy.mul_left 2).add hc
  exact hodd.tsum_eq

/-! ## The candidate Weierstrass point pair -/

/-- The `X`-coordinate of the candidate point of the Tate parametrisation: the
`x`-kernel series.  No constant normalisation is applied, so this is the raw series of
`TateCoordinateSeries`. -/
def tateWeierstrassX {K : Type*} [NormedField K] (q u : K) : K :=
  coordinateSeries q u

/-- The `Y`-coordinate of the candidate point of the Tate parametrisation: the raw
`y`-kernel series of `TateYCoordinateSeries`. -/
def tateWeierstrassY {K : Type*} [NormedField K] (q u : K) : K :=
  yCoordinateSeries q u

/-- `ℤ`-periodicity of the `X`-coordinate, transported from `coordinateSeries`. -/
theorem tateWeierstrassX_zpow_mul_parameter {K : Type*} [NormedField K] {q : K}
    (parameterNeZero : q ≠ 0) (m : ℤ) (u : K) :
    tateWeierstrassX q (q ^ m * u) = tateWeierstrassX q u :=
  coordinateSeries_zpow_mul_parameter parameterNeZero m u

/-- `ℤ`-periodicity of the `Y`-coordinate, transported from `yCoordinateSeries`. -/
theorem tateWeierstrassY_zpow_mul_parameter {K : Type*} [NormedField K] {q : K}
    (parameterNeZero : q ≠ 0) (m : ℤ) (u : K) :
    tateWeierstrassY q (q ^ m * u) = tateWeierstrassY q u :=
  yCoordinateSeries_zpow_mul_parameter parameterNeZero m u

/-- The odd coordinate of the pair is `2 * Y + X`, i.e. the already-proved
inversion-antisymmetric series.  Division-free form of `Y = (O - X)/2`. -/
theorem two_mul_tateWeierstrassY_eq_oddSeries_sub_X
    {K : Type*} [NormedField K] [CompleteSpace K] {q : K}
    (parameterNorm : ‖q‖ < 1) (u : K) :
    2 * tateWeierstrassY q u =
      inversionOddYCoordinateSeries q u - tateWeierstrassX q u := by
  simp only [tateWeierstrassY, tateWeierstrassX]
  rw [inversionOddYCoordinateSeries_eq_two_mul_yCoordinateSeries_add_coordinateSeries
    parameterNorm u]
  ring

/-- The `Y`-coordinate in the normalisation `Y = O - X/2` announced for the odd series
`O = inversionOddYCoordinateSeries`.  The division-free identity
`two_mul_tateWeierstrassY_eq_oddSeries_sub_X` is the primary statement; this is its
char-zero form. -/
theorem tateWeierstrassY_eq_half_oddSeries_sub_X
    {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K] {q : K}
    (parameterNorm : ‖q‖ < 1) (u : K) :
    tateWeierstrassY q u =
      (inversionOddYCoordinateSeries q u - tateWeierstrassX q u) / 2 := by
  have htwo : (2 : K) ≠ 0 := by norm_num
  rw [eq_div_iff htwo, mul_comm]
  exact two_mul_tateWeierstrassY_eq_oddSeries_sub_X parameterNorm u

/-! ## The canonical coefficients at the affine level -/

/-- The affine `a₁` of the canonical `q`-series curve is `1`. -/
theorem tateCanonicalAffine_a₁ {K : Type*} [NormedField K] [CharZero K] (q : K) :
    (weierstrassCurve K q).toAffine.a₁ = 1 :=
  rfl

/-- The affine `a₂` of the canonical `q`-series curve is `0`. -/
theorem tateCanonicalAffine_a₂ {K : Type*} [NormedField K] [CharZero K] (q : K) :
    (weierstrassCurve K q).toAffine.a₂ = 0 :=
  rfl

/-- The affine `a₃` of the canonical `q`-series curve is `0`. -/
theorem tateCanonicalAffine_a₃ {K : Type*} [NormedField K] [CharZero K] (q : K) :
    (weierstrassCurve K q).toAffine.a₃ = 0 :=
  rfl

/-- The affine `a₄` of the canonical `q`-series curve is the Lambert coefficient
`a4 K q`. -/
theorem tateCanonicalAffine_a₄ {K : Type*} [NormedField K] [CharZero K] (q : K) :
    (weierstrassCurve K q).toAffine.a₄ = a4 K q :=
  rfl

/-- The affine `a₆` of the canonical `q`-series curve is the Lambert coefficient
`a6 K q`. -/
theorem tateCanonicalAffine_a₆ {K : Type*} [NormedField K] [CharZero K] (q : K) :
    (weierstrassCurve K q).toAffine.a₆ = a6 K q :=
  rfl

/-! ## The Weierstrass equation as an explicit named hypothesis -/

/-- **The named normalisation hypothesis of this file.**  The pair of series
coordinates lies on the canonical `q`-series Weierstrass curve.  This is the classical
analytic (theta/sigma) input of the Tate parametrisation; it is *not* proved here and is
deliberately a visible hypothesis of every point-valued statement below. -/
def tateWeierstrassEquation {K : Type*} [NormedField K] [CharZero K] (q u : K) : Prop :=
  (weierstrassCurve K q).toAffine.Equation (tateWeierstrassX q u) (tateWeierstrassY q u)

/-- The named hypothesis in the canonical coefficients: `Y^2 + X*Y = X^3 + a4 q * X +
a6 q`, exactly as a polynomial identity in the five coefficients of
`weierstrassCurve K q`. -/
theorem tateWeierstrassEquation_iff_coefficients
    {K : Type*} [NormedField K] [CharZero K] (q u : K) :
    tateWeierstrassEquation q u ↔
      tateWeierstrassY q u ^ 2 + tateWeierstrassX q u * tateWeierstrassY q u =
        tateWeierstrassX q u ^ 3 + a4 K q * tateWeierstrassX q u + a6 K q := by
  unfold tateWeierstrassEquation
  rw [WeierstrassCurve.Affine.equation_iff,
    tateCanonicalAffine_a₁, tateCanonicalAffine_a₂, tateCanonicalAffine_a₃,
    tateCanonicalAffine_a₄, tateCanonicalAffine_a₆]
  constructor <;> intro h <;> simpa using h

/-- The canonical odd-coordinate form of the named hypothesis: the odd series
`O = 2Y + X` satisfies `O^2 = 4 X^3 + X^2 + 4 a4 X + 4 a6`.  The equivalence is proved;
only the identity itself is the remaining analytic input. -/
theorem tateWeierstrassEquation_iff_oddSeries
    {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K] {q : K}
    (parameterNorm : ‖q‖ < 1) (u : K) :
    tateWeierstrassEquation q u ↔
      inversionOddYCoordinateSeries q u ^ 2 =
        4 * tateWeierstrassX q u ^ 3 + tateWeierstrassX q u ^ 2 +
          4 * a4 K q * tateWeierstrassX q u + 4 * a6 K q := by
  have hodd : inversionOddYCoordinateSeries q u =
      2 * tateWeierstrassY q u + tateWeierstrassX q u := by
    linear_combination (-1 : K) *
      two_mul_tateWeierstrassY_eq_oddSeries_sub_X parameterNorm u
  have hfour : (4 : K) ≠ 0 := by norm_num
  rw [tateWeierstrassEquation_iff_coefficients]
  constructor
  · intro hequation
    rw [hodd]
    linear_combination 4 * hequation
  · intro hoddEquation
    rw [hodd] at hoddEquation
    have hzero : (4 : K) * (tateWeierstrassY q u ^ 2 +
        tateWeierstrassX q u * tateWeierstrassY q u -
        (tateWeierstrassX q u ^ 3 + a4 K q * tateWeierstrassX q u + a6 K q)) = 0 := by
      linear_combination hoddEquation
    exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left hfour)

/-- The named hypothesis is invariant under the full `ℤ`-period, so it descends to the
orbit quotient of the parameter. -/
theorem tateWeierstrassEquation_zpow_mul_parameter
    {K : Type*} [NormedField K] [CharZero K] {q : K} (parameterNeZero : q ≠ 0)
    (m : ℤ) (u : K) :
    tateWeierstrassEquation q (q ^ m * u) ↔ tateWeierstrassEquation q u := by
  unfold tateWeierstrassEquation
  rw [tateWeierstrassX_zpow_mul_parameter parameterNeZero m u,
    tateWeierstrassY_zpow_mul_parameter parameterNeZero m u]

/-! ## Nonsingularity: exact decomposition into the equation and the partials -/

/-- `Nonsingular` for the canonical affine curve is exactly the equation together with
non-vanishing of one of the two partial derivatives.  This records the exact strength of
the nonsingularity input used by the point-valued statements. -/
theorem tateWeierstrassNonsingular_iff_equation_and_partials
    {K : Type*} [NormedField K] [CharZero K] (q x y : K) :
    (weierstrassCurve K q).toAffine.Nonsingular x y ↔
      (weierstrassCurve K q).toAffine.Equation x y ∧
        (y - (3 * x ^ 2 + a4 K q) ≠ 0 ∨ 2 * y + x ≠ 0) := by
  rw [WeierstrassCurve.Affine.nonsingular_iff',
    tateCanonicalAffine_a₁, tateCanonicalAffine_a₂, tateCanonicalAffine_a₃,
    tateCanonicalAffine_a₄]
  constructor
  · rintro ⟨hequation, hpartials⟩
    exact ⟨hequation, by simpa using hpartials⟩
  · rintro ⟨hequation, hpartials⟩
    exact ⟨hequation, by simpa using hpartials⟩

/-- The same decomposition at the series pair, with the equation part written as the
named hypothesis `tateWeierstrassEquation`. -/
theorem tateWeierstrassPointNonsingular_iff
    {K : Type*} [NormedField K] [CharZero K] (q u : K) :
    (weierstrassCurve K q).toAffine.Nonsingular (tateWeierstrassX q u) (tateWeierstrassY q u) ↔
      tateWeierstrassEquation q u ∧
        (tateWeierstrassY q u - (3 * tateWeierstrassX q u ^ 2 + a4 K q) ≠ 0 ∨
          2 * tateWeierstrassY q u + tateWeierstrassX q u ≠ 0) := by
  have h := tateWeierstrassNonsingular_iff_equation_and_partials q
    (tateWeierstrassX q u) (tateWeierstrassY q u)
  unfold tateWeierstrassEquation
  exact h

/-! ## The point-valued form -/

/-- The candidate point of the canonical curve attached to the series pair, given the
nonsingularity data.  This is the value of the Tate point map before quotienting by the
`q^ℤ`-action. -/
def tateWeierstrassPointAt {K : Type*} [NormedField K] [CharZero K] (q u : K)
    (hpoint : (weierstrassCurve K q).toAffine.Nonsingular
      (tateWeierstrassX q u) (tateWeierstrassY q u)) :
    (weierstrassCurve K q).toAffine.Point :=
  WeierstrassCurve.Affine.Point.some (tateWeierstrassX q u) (tateWeierstrassY q u) hpoint

/-- The candidate point is `ℤ`-periodic in the parameter.  The two nonsingularity proofs
are arbitrary proofs of a proposition, so the statement compares the points themselves. -/
theorem tateWeierstrassPointAt_zpow_mul_parameter
    {K : Type*} [NormedField K] [CharZero K] {q : K} (parameterNeZero : q ≠ 0)
    (m : ℤ) (u : K)
    (hperiod : (weierstrassCurve K q).toAffine.Nonsingular
      (tateWeierstrassX q (q ^ m * u)) (tateWeierstrassY q (q ^ m * u)))
    (hbase : (weierstrassCurve K q).toAffine.Nonsingular
      (tateWeierstrassX q u) (tateWeierstrassY q u)) :
    tateWeierstrassPointAt q (q ^ m * u) hperiod = tateWeierstrassPointAt q u hbase := by
  change WeierstrassCurve.Affine.Point.some (tateWeierstrassX q (q ^ m * u))
      (tateWeierstrassY q (q ^ m * u)) hperiod =
    WeierstrassCurve.Affine.Point.some (tateWeierstrassX q u) (tateWeierstrassY q u) hbase
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨tateWeierstrassX_zpow_mul_parameter parameterNeZero m u,
    tateWeierstrassY_zpow_mul_parameter parameterNeZero m u⟩

end

end LeanFormal.IUT.TateCurve
