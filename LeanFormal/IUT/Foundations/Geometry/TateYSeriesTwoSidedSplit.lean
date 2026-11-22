/-
  Two-sided split of the Tate y-series.

  `TateYCoordinateSeries` builds the integer-indexed y-series directly, and the
  repaired `RigidTateSeries` writes one-sided `yPositiveSeries` /
  `yNegativeSeries` over its own parameter type.  This file isolates the
  one-sided halves of the two integer series of `TateYCoordinateSeries` -- the
  even kernel `z ^ 2 / (1 - z) ^ 3` and the inversion-antisymmetric kernel --
  and proves the splitting identity

      sum_{n : Z} kernel (q ^ n * u)
        = (sum_{n : N} kernel (q ^ n * u)) + (sum_{n : N} kernel (q ^ (-((n : ℤ) + 1)) * u))

  for both kernels, using Mathlib's `tsum_of_nat_of_neg_add_one`.  Convergence
  of the two halves is `yCoordinateKernel_nat_summable` /
  `yCoordinateKernel_neg_summable` and their inversion-antisymmetric
  companions, already proved in `TateYCoordinateSeries`.

  Historical note: an earlier coordination report recorded this splitting as a
  missing Mathlib lemma named `tsum_int_eq_tsum_nat_add_neg`; the lemma exists
  in `Mathlib.Topology.Algebra.InfiniteSum.NatInt` under the name
  `tsum_of_nat_of_neg_add_one` (and the "iff" form
  `summable_int_iff_summable_nat_and_neg_add_one`).
-/

import LeanFormal.IUT.Foundations.Geometry.TateYCoordinateSeries
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

namespace LeanFormal.IUT.TateCurve

noncomputable section

/-! ## The two halves of the even-kernel y-series -/

/-- The nonnegative-exponent half of the integer-indexed Tate y-series. -/
def yPositivePart {K : Type*} [NormedField K] (q u : K) : K :=
  ∑' n : ℕ, yCoordinateKernel (q ^ (n : ℤ) * u)

/-- The strictly negative-exponent half of the integer-indexed Tate y-series,
indexed by `n : ℕ` at exponents `-(n + 1)`. -/
def yNegativePart {K : Type*} [NormedField K] (q u : K) : K :=
  ∑' n : ℕ, yCoordinateKernel (q ^ (-((n : ℤ) + 1)) * u)

/-- The integer-indexed y-series is the sum of its nonnegative- and
negative-exponent halves. -/
theorem yCoordinateSeries_eq_yPositivePart_add_yNegativePart
    {K : Type*} [NormedField K] [CompleteSpace K] {q : K}
    (parameterNorm : ‖q‖ < 1) (u : K) :
    yCoordinateSeries q u = yPositivePart q u + yNegativePart q u := by
  have hpos : Summable (fun n : ℕ => yCoordinateKernel (q ^ (n : ℤ) * u)) := by
    simpa only [zpow_natCast] using yCoordinateKernel_nat_summable parameterNorm u
  have hneg : Summable (fun n : ℕ => yCoordinateKernel (q ^ (-((n : ℤ) + 1)) * u)) := by
    have hshift :=
      (summable_nat_add_iff 1).mpr (yCoordinateKernel_neg_summable (q := q) parameterNorm u)
    simpa only [Nat.cast_add, Nat.cast_one] using hshift
  unfold yCoordinateSeries yPositivePart yNegativePart
  exact tsum_of_nat_of_neg_add_one hpos hneg

/-! ## The two halves of the inversion-antisymmetric y-series -/

/-- The nonnegative-exponent half of the inversion-antisymmetric y-series. -/
def inversionOddYPositivePart {K : Type*} [NormedField K] (q u : K) : K :=
  ∑' n : ℕ, inversionOddYCoordinateKernel (q ^ (n : ℤ) * u)

/-- The strictly negative-exponent half of the inversion-antisymmetric
y-series, indexed by `n : ℕ` at exponents `-(n + 1)`. -/
def inversionOddYNegativePart {K : Type*} [NormedField K] (q u : K) : K :=
  ∑' n : ℕ, inversionOddYCoordinateKernel (q ^ (-((n : ℤ) + 1)) * u)

/-- The integer-indexed inversion-antisymmetric y-series is the sum of its
nonnegative- and negative-exponent halves. -/
theorem inversionOddYCoordinateSeries_eq_inversionOddYPositivePart_add_inversionOddYNegativePart
    {K : Type*} [NormedField K] [CompleteSpace K] {q : K}
    (parameterNorm : ‖q‖ < 1) (u : K) :
    inversionOddYCoordinateSeries q u =
      inversionOddYPositivePart q u + inversionOddYNegativePart q u := by
  have hpos : Summable (fun n : ℕ => inversionOddYCoordinateKernel (q ^ (n : ℤ) * u)) := by
    simpa only [zpow_natCast] using
      inversionOddYCoordinateKernel_nat_summable parameterNorm u
  have hneg₀ : Summable
      (fun n : ℕ => inversionOddYCoordinateKernel (q ^ (-(n : ℤ)) * u)) := by
    have hf : Summable (fun n : ℕ => inversionOddYCoordinateKernel (q ^ n * u⁻¹)) :=
      inversionOddYCoordinateKernel_nat_summable parameterNorm u⁻¹
    refine (hf.neg).congr (fun n => ?_)
    have hz : q ^ (-(n : ℤ)) * u = (q ^ (n : ℤ) * u⁻¹)⁻¹ := by
      rw [mul_inv_rev, inv_inv, ← zpow_neg, mul_comm]
    rw [hz, inversionOddYCoordinateKernel_inv, zpow_natCast]
  have hneg : Summable (fun n : ℕ => inversionOddYCoordinateKernel (q ^ (-((n : ℤ) + 1)) * u)) := by
    have hshift := (summable_nat_add_iff 1).mpr hneg₀
    simpa only [Nat.cast_add, Nat.cast_one] using hshift
  unfold inversionOddYCoordinateSeries inversionOddYPositivePart inversionOddYNegativePart
  exact tsum_of_nat_of_neg_add_one hpos hneg

/-! ## The two halves of the integer-indexed x-series -/

/-- The nonnegative-exponent half of the integer-indexed Tate x-series. -/
def coordinatePositivePart {K : Type*} [NormedField K] (q u : K) : K :=
  ∑' n : ℕ, coordinateKernel (q ^ (n : ℤ) * u)

/-- The strictly negative-exponent half of the integer-indexed Tate x-series,
indexed by `n : ℕ` at exponents `-(n + 1)`. -/
def coordinateNegativePart {K : Type*} [NormedField K] (q u : K) : K :=
  ∑' n : ℕ, coordinateKernel (q ^ (-((n : ℤ) + 1)) * u)

/-- The integer-indexed x-series is the sum of its nonnegative- and
negative-exponent halves.  The negative half is controlled by the inversion
invariance of the x-kernel, exactly as in `coordinateKernel_int_summable`. -/
theorem coordinateSeries_eq_coordinatePositivePart_add_coordinateNegativePart
    {K : Type*} [NormedField K] [CompleteSpace K] {q : K}
    (parameterNorm : ‖q‖ < 1) (u : K) :
    coordinateSeries q u = coordinatePositivePart q u + coordinateNegativePart q u := by
  have hpos : Summable (fun n : ℕ => coordinateKernel (q ^ (n : ℤ) * u)) := by
    simpa only [zpow_natCast] using coordinateKernel_nat_summable parameterNorm u
  have hneg₀ : Summable (fun n : ℕ => coordinateKernel (q ^ (-(n : ℤ)) * u)) := by
    refine (coordinateKernel_nat_summable parameterNorm u⁻¹).congr (fun n => ?_)
    rw [← coordinateKernel_inv (q ^ (-(n : ℤ)) * u)]
    simp only [mul_inv_rev, zpow_neg, zpow_natCast, inv_inv]
    rw [mul_comm]
  have hneg : Summable (fun n : ℕ => coordinateKernel (q ^ (-((n : ℤ) + 1)) * u)) := by
    have hshift := (summable_nat_add_iff 1).mpr hneg₀
    simpa only [Nat.cast_add, Nat.cast_one] using hshift
  unfold coordinateSeries coordinatePositivePart coordinateNegativePart
  exact tsum_of_nat_of_neg_add_one hpos hneg

end

end LeanFormal.IUT.TateCurve