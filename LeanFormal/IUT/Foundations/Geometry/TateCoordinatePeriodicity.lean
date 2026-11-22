/-
  Period and inversion identities for the Tate coordinate series.

  `TateCoordinateSeries` proves the `+1` periodicity of the x-coordinate series.
  This file records the scalar symmetries of the actual series coordinates:

  * the x-coordinate series is even under `u ↦ u⁻¹` (the untwisted kernel law);
  * the y-coordinate series `∑ yCoordinateKernel (q^n u)` has the honest twisted
    inversion law, because `yCoordinateKernel` is not inversion-invariant;
  * the inversion-antisymmetric y-series is odd under `u ↦ u⁻¹`;
  * all three coordinates are invariant under the full `ℤ`-period `u ↦ q^m u`,
    generalising the `m = 1` statement of `TateCoordinateSeries`, and the
    individual coefficients move by index shift.

  Every identity below is stated for the concrete kernels proved in
  `TateCoordinateSeries` and `TateYCoordinateSeries`; no convergence is invented
  and no summability hypothesis is needed for the reindexing identities.
-/

import LeanFormal.IUT.Foundations.Geometry.TateYCoordinateSeries
import Mathlib.Tactic

namespace LeanFormal.IUT.TateCurve

noncomputable section

/-! ## x-coordinate: period and inversion -/

/-- Coefficient-level `q`-scaling of the x-series: the `n`-th coefficient of the
series at parameter `q * u` is the `(n+1)`-st coefficient at parameter `u`. -/
theorem coordinateKernel_zpow_scale
    {K : Type*} [Field K] {q : K} (parameterNeZero : q ≠ 0)
    (n : ℤ) (u : K) :
    coordinateKernel (q ^ n * (q * u)) = coordinateKernel (q ^ (n + 1) * u) := by
  rw [zpow_add₀ parameterNeZero, zpow_one, mul_assoc]

/-- Full `ℤ`-period of the x-coordinate series; the `m = 1` case is
`coordinateSeries_mul_parameter`. -/
theorem coordinateSeries_zpow_mul_parameter
    {K : Type*} [NormedField K] {q : K} (parameterNeZero : q ≠ 0)
    (m : ℤ) (u : K) :
    coordinateSeries q (q ^ m * u) = coordinateSeries q u := by
  unfold coordinateSeries
  calc
    (∑' n : ℤ, coordinateKernel (q ^ n * (q ^ m * u))) =
        ∑' n : ℤ, coordinateKernel (q ^ (n + m) * u) := by
      apply tsum_congr
      intro n
      rw [zpow_add₀ parameterNeZero, mul_assoc]
    _ = ∑' n : ℤ, coordinateKernel (q ^ n * u) :=
      (Equiv.addRight m).tsum_eq (fun n : ℤ => coordinateKernel (q ^ n * u))

/-- The x-coordinate series is even under inversion of the parameter. -/
theorem coordinateSeries_inv
    {K : Type*} [NormedField K] (q u : K) :
    coordinateSeries q u⁻¹ = coordinateSeries q u := by
  unfold coordinateSeries
  calc
    (∑' n : ℤ, coordinateKernel (q ^ n * u⁻¹)) =
        ∑' n : ℤ, coordinateKernel (q ^ (-n) * u) := by
      apply tsum_congr
      intro n
      have hz : q ^ n * u⁻¹ = (q ^ (-n) * u)⁻¹ := by
        rw [zpow_neg, mul_inv_rev, inv_inv, mul_comm]
      rw [hz, coordinateKernel_inv]
    _ = ∑' n : ℤ, coordinateKernel (q ^ n * u) := by
      simpa only [Equiv.neg_apply] using
        (Equiv.neg ℤ).tsum_eq (fun n : ℤ => coordinateKernel (q ^ n * u))

/-! ## y-coordinate: period, coefficient shift, twisted inversion -/

/-- Coefficient-level `q`-scaling of the y-series. -/
theorem yCoordinateKernel_zpow_scale
    {K : Type*} [Field K] {q : K} (parameterNeZero : q ≠ 0)
    (n : ℤ) (u : K) :
    yCoordinateKernel (q ^ n * (q * u)) = yCoordinateKernel (q ^ (n + 1) * u) := by
  rw [zpow_add₀ parameterNeZero, zpow_one, mul_assoc]

/-- Full `ℤ`-period of the y-coordinate series; the `m = 1` case is
`yCoordinateSeries_mul_parameter`. -/
theorem yCoordinateSeries_zpow_mul_parameter
    {K : Type*} [NormedField K] {q : K} (parameterNeZero : q ≠ 0)
    (m : ℤ) (u : K) :
    yCoordinateSeries q (q ^ m * u) = yCoordinateSeries q u := by
  unfold yCoordinateSeries
  calc
    (∑' n : ℤ, yCoordinateKernel (q ^ n * (q ^ m * u))) =
        ∑' n : ℤ, yCoordinateKernel (q ^ (n + m) * u) := by
      apply tsum_congr
      intro n
      rw [zpow_add₀ parameterNeZero, mul_assoc]
    _ = ∑' n : ℤ, yCoordinateKernel (q ^ n * u) :=
      (Equiv.addRight m).tsum_eq (fun n : ℤ => yCoordinateKernel (q ^ n * u))

/-- The y-coordinate series twisted by the character `n ↦ q^{-n}`.  This is the
honest inversion transform of the `z^2/(1-z)^3` series: that kernel is not
inversion-invariant, so its inversion law cannot be a pure sign. -/
noncomputable def yCoordinateSeriesTwisted
    {K : Type*} [NormedField K] (q u : K) : K :=
  ∑' n : ℤ, q ^ (-n) * yCoordinateKernel (q ^ n * u)

/-- The honest inversion law of the y-coordinate series: inversion contributes the
scalar `-u⁻¹` and the `q^{-n}` twist of the coefficients. -/
theorem yCoordinateSeries_inv
    {K : Type*} [NormedField K] (q u : K) :
    yCoordinateSeries q u⁻¹ = -(u⁻¹) * yCoordinateSeriesTwisted q u := by
  unfold yCoordinateSeries yCoordinateSeriesTwisted
  calc
    (∑' n : ℤ, yCoordinateKernel (q ^ n * u⁻¹)) =
        ∑' n : ℤ, -(u⁻¹) * (q ^ n * yCoordinateKernel (q ^ (-n) * u)) := by
      apply tsum_congr
      intro n
      have hz : q ^ n * u⁻¹ = (q ^ (-n) * u)⁻¹ := by
        rw [zpow_neg, mul_inv_rev, inv_inv, mul_comm]
      rw [hz, yCoordinateKernel_inv, ← hz]
      ring
    _ = ∑' n : ℤ, -(u⁻¹) * (q ^ (-n) * yCoordinateKernel (q ^ n * u)) := by
      have hneg := (Equiv.neg ℤ).tsum_eq
        (fun n : ℤ => -(u⁻¹) * (q ^ n * yCoordinateKernel (q ^ (-n) * u)))
      simpa only [Equiv.neg_apply, neg_neg] using hneg.symm
    _ = -(u⁻¹) * ∑' n : ℤ, q ^ (-n) * yCoordinateKernel (q ^ n * u) := by
      rw [tsum_mul_left]

/-! ## Inversion-antisymmetric y-coordinate: period and inversion -/

/-- Full `ℤ`-period of the inversion-antisymmetric y-series. -/
theorem inversionOddYCoordinateSeries_zpow_mul_parameter
    {K : Type*} [NormedField K] {q : K} (parameterNeZero : q ≠ 0)
    (m : ℤ) (u : K) :
    inversionOddYCoordinateSeries q (q ^ m * u) = inversionOddYCoordinateSeries q u := by
  unfold inversionOddYCoordinateSeries
  calc
    (∑' n : ℤ, inversionOddYCoordinateKernel (q ^ n * (q ^ m * u))) =
        ∑' n : ℤ, inversionOddYCoordinateKernel (q ^ (n + m) * u) := by
      apply tsum_congr
      intro n
      rw [zpow_add₀ parameterNeZero, mul_assoc]
    _ = ∑' n : ℤ, inversionOddYCoordinateKernel (q ^ n * u) :=
      (Equiv.addRight m).tsum_eq
        (fun n : ℤ => inversionOddYCoordinateKernel (q ^ n * u))

/-- The inversion-antisymmetric y-series is odd under inversion of the parameter. -/
theorem inversionOddYCoordinateSeries_inv
    {K : Type*} [NormedField K] (q u : K) :
    inversionOddYCoordinateSeries q u⁻¹ = -inversionOddYCoordinateSeries q u := by
  unfold inversionOddYCoordinateSeries
  calc
    (∑' n : ℤ, inversionOddYCoordinateKernel (q ^ n * u⁻¹)) =
        ∑' n : ℤ, -inversionOddYCoordinateKernel (q ^ (-n) * u) := by
      apply tsum_congr
      intro n
      have hz : q ^ n * u⁻¹ = (q ^ (-n) * u)⁻¹ := by
        rw [zpow_neg, mul_inv_rev, inv_inv, mul_comm]
      rw [hz, inversionOddYCoordinateKernel_inv]
    _ = -(∑' n : ℤ, inversionOddYCoordinateKernel (q ^ (-n) * u)) := tsum_neg
    _ = -(∑' n : ℤ, inversionOddYCoordinateKernel (q ^ n * u)) := by
      have hneg : (∑' n : ℤ, inversionOddYCoordinateKernel (q ^ (-n) * u)) =
          ∑' n : ℤ, inversionOddYCoordinateKernel (q ^ n * u) := by
        simpa only [Equiv.neg_apply] using
          (Equiv.neg ℤ).tsum_eq
            (fun n : ℤ => inversionOddYCoordinateKernel (q ^ n * u))
      exact congrArg Neg.neg hneg

end

end LeanFormal.IUT.TateCurve
