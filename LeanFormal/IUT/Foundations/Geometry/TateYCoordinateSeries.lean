/-
  The Tate y-coordinate series.

  The x-coordinate kernel `z ↦ z/(1-z)^2` of `TateCoordinateSeries` is the proven
  analytic kernel of the Tate coordinate.  This file supplies the genuinely missing
  y-side.  The kernel that `RigidTateSeries` writes down for the y terms is

      yCoordinateKernel z = z^2 / (1-z)^3,

  and everything below is stated for that kernel: the honest inversion law
  (`yCoordinateKernel z⁻¹ = -(z⁻¹) * yCoordinateKernel z`, the y-analogue of
  `coordinateKernel_inv`), the small- and large-argument norm bounds, convergence of
  the natural- and integer-indexed series, the q-periodicity of the resulting
  coordinate, and its compatibility with continuous ring homomorphisms.

  A second, inversion-antisymmetric kernel `inversionOddYCoordinateKernel z =
  z * (1+z) / (1-z)^3` is treated afterwards: it is the y-kernel that is odd under
  `z ↦ z⁻¹`, i.e. the companion of the even x-coordinate in the point-valued
  uniformization.  No calculus statement is made about it.

  `RigidTateSeries.lean` does not compile under the pinned mathlib (see the
  coordination log), so the one-sided `yPositiveSeries`/`yNegativeSeries` are not
  importable and are not referenced here; the two-sided integer series is built
  directly, exactly as `TateCoordinateSeries` builds the x-series.
-/

import LeanFormal.IUT.Foundations.Geometry.TateCoordinateSeries
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

namespace LeanFormal.IUT.TateCurve

noncomputable section

/-! ## The y-kernel and its inversion law -/

/-- The rational kernel of the Tate y-coordinate Laurent series, matching the
`z^2/(1-z)^3` summands of `RigidTateSeries`. -/
def yCoordinateKernel {K : Type*} [Field K] (z : K) : K :=
  z ^ 2 / (1 - z) ^ 3

/-- The y-kernel is the x-kernel with one further factor `z/(1-z)`. -/
theorem yCoordinateKernel_eq_mul_coordinateKernel
    {K : Type*} [Field K] (z : K) :
    yCoordinateKernel z = z * coordinateKernel z / (1 - z) := by
  by_cases h : (1 : K) - z = 0
  · have hz : z = 1 := (sub_eq_zero.mp h).symm
    rw [hz]
    simp [yCoordinateKernel, coordinateKernel]
  · unfold yCoordinateKernel coordinateKernel
    field_simp

/-- On the pole-excluded parameter domain every y-denominator is nonzero. -/
theorem coordinatePoleExclusion_yDenominator_ne_zero
    {K : Type*} [Field K] {q u : K}
    (poleExclusion : coordinatePoleExclusion q u) (n : ℤ) :
    (1 - q ^ n * u) ^ 3 ≠ 0 :=
  pow_ne_zero 3 (sub_ne_zero.mpr (poleExclusion n).symm)

/-- The honest inversion law of the y-kernel: it is not inversion-invariant, but
inversion contributes the factor `-z⁻¹`.  The identity holds for every `z`, since the
exceptional cases `z = 0` and `z = 1` totalise to `0` on both sides. -/
theorem yCoordinateKernel_inv
    {K : Type*} [Field K] (z : K) :
    yCoordinateKernel z⁻¹ = -(z⁻¹) * yCoordinateKernel z := by
  by_cases h0 : z = 0
  · rw [h0]
    simp [yCoordinateKernel]
  by_cases h1 : z = 1
  · rw [h1]
    simp [yCoordinateKernel]
  have hden : (1 : K) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have hdeninv : (1 : K) - z⁻¹ ≠ 0 := by
    intro hc
    have hz : z⁻¹ = 1 := (sub_eq_zero.mp hc).symm
    exact h1 (by rw [← inv_inv z, hz, inv_one])
  unfold yCoordinateKernel
  field_simp [h0, hden, hdeninv]
  ring

/-! ## Norm bounds -/

/-- Small-argument bound: the y-kernel is bounded by `8 ‖z‖^2`. -/
theorem yCoordinateKernel_norm_le
    {K : Type*} [NormedField K] {z : K} (smallNorm : ‖z‖ ≤ 1 / 2) :
    ‖yCoordinateKernel z‖ ≤ 8 * ‖z‖ ^ 2 := by
  have denominatorLowerBound : (1 / 2 : ℝ) ≤ ‖(1 : K) - z‖ := by
    have normDifferenceBound := norm_sub_norm_le (1 : K) z
    rw [norm_one] at normDifferenceBound
    linarith
  have denominatorCubeLowerBound : (1 / 8 : ℝ) ≤ ‖(1 : K) - z‖ ^ 3 := by
    have hcube := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2)
      denominatorLowerBound 3
    norm_num at hcube
    exact hcube
  rw [yCoordinateKernel, norm_div, norm_pow, norm_pow]
  apply (div_le_iff₀
    (pow_pos (by linarith : 0 < ‖(1 : K) - z‖) 3)).2
  nlinarith [norm_nonneg z, denominatorCubeLowerBound, sq_nonneg ‖z‖]

/-- Large-argument bound: the y-kernel decays like `1/‖z‖`. -/
theorem yCoordinateKernel_norm_le_inv
    {K : Type*} [NormedField K] {z : K} (largeNorm : 2 ≤ ‖z‖) :
    ‖yCoordinateKernel z‖ ≤ 8 * ‖z‖⁻¹ := by
  have hzpos : 0 < ‖z‖ := by linarith
  have denominatorLowerBound : ‖z‖ / 2 ≤ ‖(1 : K) - z‖ := by
    have h := norm_sub_norm_le z (1 : K)
    rw [norm_one, norm_sub_rev] at h
    linarith
  have denominatorCubeLowerBound : (‖z‖ / 2) ^ 3 ≤ ‖(1 : K) - z‖ ^ 3 :=
    pow_le_pow_left₀ (by positivity) denominatorLowerBound 3
  rw [yCoordinateKernel, norm_div, norm_pow, norm_pow]
  rw [div_le_iff₀ (pow_pos (by linarith : 0 < ‖(1 : K) - z‖) 3)]
  have key : (8 * ‖z‖⁻¹) * (‖z‖ / 2) ^ 3 = ‖z‖ ^ 2 := by
    field_simp
    ring
  nlinarith [norm_nonneg ((1 : K) - z), denominatorCubeLowerBound, key,
    inv_nonneg.mpr (le_of_lt hzpos)]

/-! ## Convergence -/

/-- The natural-indexed y-series converges. -/
theorem yCoordinateKernel_nat_summable
    {K : Type*} [NormedField K] [CompleteSpace K] {q : K}
    (parameterNorm : ‖q‖ < 1) (u : K) :
    Summable (fun n : ℕ => yCoordinateKernel (q ^ n * u)) := by
  have parameterNormSq : ‖q‖ ^ 2 < 1 := by nlinarith [norm_nonneg q]
  have kernelArgumentNormTendsto :
      Filter.Tendsto (fun n : ℕ => ‖q ^ n * u‖) Filter.atTop (nhds 0) := by
    simpa using
      ((tendsto_pow_atTop_nhds_zero_of_norm_lt_one parameterNorm).mul_const u).norm
  have eventuallySmallNorm :
      ∀ᶠ n : ℕ in Filter.atTop, ‖q ^ n * u‖ < 1 / 2 :=
    Filter.Tendsto.eventually_lt_const (by norm_num) kernelArgumentNormTendsto
  have geometricMajorantSummable :
      Summable (fun n : ℕ => (8 * ‖u‖ ^ 2) * (‖q‖ ^ 2) ^ n) :=
    Summable.mul_left (8 * ‖u‖ ^ 2)
      (summable_geometric_of_lt_one (sq_nonneg ‖q‖) parameterNormSq)
  apply geometricMajorantSummable.of_norm_bounded_eventually
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventuallySmallNorm] with n smallNorm
  calc
    ‖yCoordinateKernel (q ^ n * u)‖ ≤ 8 * ‖q ^ n * u‖ ^ 2 :=
      yCoordinateKernel_norm_le smallNorm.le
    _ = (8 * ‖u‖ ^ 2) * (‖q‖ ^ 2) ^ n := by
      rw [norm_mul, norm_pow, mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm n 2]
      ring

/-- The negative-index half of the y-series converges; this is where the y-side
genuinely differs from the x-side: the inversion law carries the growing factor
`-q^{-n}u`, which is compensated by the `z^{-2}` decay of the kernel at large
argument. -/
theorem yCoordinateKernel_neg_summable
    {K : Type*} [NormedField K] [CompleteSpace K] {q : K}
    (parameterNorm : ‖q‖ < 1) (u : K) :
    Summable (fun n : ℕ => yCoordinateKernel (q ^ (-(n : ℤ)) * u)) := by
  by_cases hu : u = 0
  · rw [hu]
    refine (summable_zero : Summable (fun _ : ℕ => (0 : K))).congr (fun n => ?_)
    simp [yCoordinateKernel]
  by_cases hq : q = 0
  · rw [hq]
    refine (summable_nat_add_iff 1).mp ?_
    refine (summable_zero : Summable (fun _ : ℕ => (0 : K))).congr (fun n => ?_)
    have hz : (0 : K) ^ (-((n + 1 : ℕ) : ℤ)) = 0 := by
      rw [zpow_neg, zpow_natCast, zero_pow (Nat.succ_ne_zero n), inv_zero]
    rw [hz, zero_mul]
    simp [yCoordinateKernel]
  · have hqnorm : ‖q‖ ≠ 0 := norm_ne_zero_iff.mpr hq
    have hunorm : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
    have hrel : ∀ n : ℕ, yCoordinateKernel (q ^ (-(n : ℤ)) * u)
        = -(q ^ (-(n : ℤ)) * u) * yCoordinateKernel (q ^ (n : ℤ) * u⁻¹) := by
      intro n
      have hz : (q ^ (n : ℤ) * u⁻¹)⁻¹ = q ^ (-(n : ℤ)) * u := by
        rw [mul_inv_rev, inv_inv, ← zpow_neg, mul_comm]
      rw [← hz, yCoordinateKernel_inv]
    have hgeom : Summable (fun n : ℕ => 8 * ‖q ^ (n : ℤ) * u⁻¹‖) := by
      have hbase : Summable (fun n : ℕ => (8 * ‖u‖⁻¹) * ‖q‖ ^ n) :=
        Summable.mul_left (8 * ‖u‖⁻¹)
          (summable_geometric_of_lt_one (norm_nonneg q) parameterNorm)
      refine hbase.congr (fun n => ?_)
      rw [norm_mul, norm_zpow, norm_inv, zpow_natCast]
      ring
    have htend :
        Filter.Tendsto (fun n : ℕ => ‖q ^ n * u⁻¹‖) Filter.atTop (nhds 0) := by
      simpa using
        ((tendsto_pow_atTop_nhds_zero_of_norm_lt_one parameterNorm).mul_const u⁻¹).norm
    have hev : ∀ᶠ n : ℕ in Filter.atTop, ‖q ^ n * u⁻¹‖ < 1 / 2 :=
      Filter.Tendsto.eventually_lt_const (by norm_num) htend
    apply hgeom.of_norm_bounded_eventually
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [hev] with n hn
    have hprod : ‖q ^ (-(n : ℤ)) * u‖ * ‖q ^ (n : ℤ) * u⁻¹‖ = 1 := by
      rw [norm_mul, norm_mul, norm_zpow, norm_zpow, norm_inv]
      rw [show ‖q‖ ^ (-(n : ℤ)) = (‖q‖ ^ n)⁻¹ by rw [zpow_neg, zpow_natCast],
        zpow_natCast]
      field_simp [pow_ne_zero n hqnorm, hunorm]
    have hn' : ‖q ^ (n : ℤ) * u⁻¹‖ < 1 / 2 := by
      simpa only [zpow_natCast] using hn
    calc
      ‖yCoordinateKernel (q ^ (-(n : ℤ)) * u)‖
          = ‖q ^ (-(n : ℤ)) * u‖ * ‖yCoordinateKernel (q ^ (n : ℤ) * u⁻¹)‖ := by
            rw [hrel n, norm_mul, norm_neg]
      _ ≤ ‖q ^ (-(n : ℤ)) * u‖ * (8 * ‖q ^ (n : ℤ) * u⁻¹‖ ^ 2) :=
            mul_le_mul_of_nonneg_left (yCoordinateKernel_norm_le hn'.le) (norm_nonneg _)
      _ = 8 * ‖q ^ (n : ℤ) * u⁻¹‖ := by
            calc
              ‖q ^ (-(n : ℤ)) * u‖ * (8 * ‖q ^ (n : ℤ) * u⁻¹‖ ^ 2)
                  = 8 * (‖q ^ (-(n : ℤ)) * u‖ * ‖q ^ (n : ℤ) * u⁻¹‖)
                      * ‖q ^ (n : ℤ) * u⁻¹‖ := by ring
              _ = 8 * ‖q ^ (n : ℤ) * u⁻¹‖ := by rw [hprod]; ring

/-- The two-sided y-series converges. -/
theorem yCoordinateKernel_int_summable
    {K : Type*} [NormedField K] [CompleteSpace K] {q : K}
    (parameterNorm : ‖q‖ < 1) (u : K) :
    Summable (fun n : ℤ => yCoordinateKernel (q ^ n * u)) := by
  apply summable_int_iff_summable_nat_and_neg.mpr
  refine ⟨?_, ?_⟩
  · simpa only [zpow_natCast] using yCoordinateKernel_nat_summable parameterNorm u
  · simpa only using yCoordinateKernel_neg_summable (q := q) parameterNorm u

/-! ## The y-coordinate series, its periodicity and naturality -/

/-- The integer-indexed Tate y-coordinate series, the y-analogue of
`coordinateSeries`. -/
noncomputable def yCoordinateSeries {K : Type*} [NormedField K] (q u : K) : K :=
  ∑' n : ℤ, yCoordinateKernel (q ^ n * u)

/-- `q`-scaling of the parameter leaves the y-coordinate series unchanged. -/
theorem yCoordinateSeries_mul_parameter
    {K : Type*} [NormedField K] {q : K} (parameterNeZero : q ≠ 0) (u : K) :
    yCoordinateSeries q (q * u) = yCoordinateSeries q u := by
  unfold yCoordinateSeries
  calc
    (∑' n : ℤ, yCoordinateKernel (q ^ n * (q * u))) =
        ∑' n : ℤ, yCoordinateKernel (q ^ (n + 1) * u) := by
      apply tsum_congr
      intro n
      rw [zpow_add₀ parameterNeZero, zpow_one, mul_assoc]
    _ = ∑' n : ℤ, yCoordinateKernel (q ^ n * u) :=
      (Equiv.addRight (1 : ℤ)).tsum_eq (fun n : ℤ => yCoordinateKernel (q ^ n * u))

/-- The y-kernel is compatible with ring homomorphisms of fields. -/
theorem yCoordinateKernel_map
    {E : Type*} {F : Type*} [Field E] [Field F]
    (fieldHom : E →+* F) (z : E) :
    fieldHom (yCoordinateKernel z) = yCoordinateKernel (fieldHom z) := by
  simp only [yCoordinateKernel, map_div₀, map_pow, map_sub, map_one]

/-- The y-coordinate series is natural in continuous ring homomorphisms between
complete normed fields. -/
theorem yCoordinateSeries_map
    {E : Type*} {F : Type*} [NormedField E] [CompleteSpace E] [NormedField F]
    (fieldHom : E →+* F) (homContinuous : Continuous fieldHom)
    {q : E} (parameterNorm : ‖q‖ < 1) (u : E) :
    fieldHom (yCoordinateSeries q u) = yCoordinateSeries (fieldHom q) (fieldHom u) := by
  have sourceHasSum :
      HasSum (fun n : ℤ => yCoordinateKernel (q ^ n * u)) (yCoordinateSeries q u) :=
    (yCoordinateKernel_int_summable parameterNorm u).hasSum
  have transportedHasSum := hasSum_int_map_ringHom fieldHom homContinuous sourceHasSum
  have mappedHasSum :
      HasSum (fun n : ℤ => yCoordinateKernel ((fieldHom q) ^ n * fieldHom u))
        (fieldHom (yCoordinateSeries q u)) := by
    simpa only [yCoordinateKernel_map, map_mul, map_zpow₀] using transportedHasSum
  exact mappedHasSum.tsum_eq.symm

/-! ## The inversion-antisymmetric y-kernel -/

/-- The y-kernel that is odd under `z ↦ z⁻¹`; its `ℤ`-series is the second
coordinate that pairs with the even x-coordinate under inversion of the Tate
parameter. -/
def inversionOddYCoordinateKernel {K : Type*} [Field K] (z : K) : K :=
  z * (1 + z) / (1 - z) ^ 3

/-- The inversion-antisymmetric y-kernel is odd under `z ↦ z⁻¹`, for every `z`. -/
theorem inversionOddYCoordinateKernel_inv
    {K : Type*} [Field K] (z : K) :
    inversionOddYCoordinateKernel z⁻¹ = -inversionOddYCoordinateKernel z := by
  by_cases h0 : z = 0
  · rw [h0]
    simp [inversionOddYCoordinateKernel]
  by_cases h1 : z = 1
  · rw [h1]
    simp [inversionOddYCoordinateKernel]
  have hden : (1 : K) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have hdeninv : (1 : K) - z⁻¹ ≠ 0 := by
    intro hc
    have hz : z⁻¹ = 1 := (sub_eq_zero.mp hc).symm
    exact h1 (by rw [← inv_inv z, hz, inv_one])
  unfold inversionOddYCoordinateKernel
  field_simp [h0, hden, hdeninv]
  ring

/-- Small-argument bound for the inversion-antisymmetric kernel. -/
theorem inversionOddYCoordinateKernel_norm_le
    {K : Type*} [NormedField K] {z : K} (smallNorm : ‖z‖ ≤ 1 / 2) :
    ‖inversionOddYCoordinateKernel z‖ ≤ 12 * ‖z‖ := by
  have hden : (1 / 2 : ℝ) ≤ ‖(1 : K) - z‖ := by
    have normDifferenceBound := norm_sub_norm_le (1 : K) z
    rw [norm_one] at normDifferenceBound
    linarith
  have hden3 : (1 / 8 : ℝ) ≤ ‖(1 : K) - z‖ ^ 3 := by
    have hcube := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hden 3
    norm_num at hcube
    exact hcube
  have hnum : ‖(1 : K) + z‖ ≤ 3 / 2 := by
    calc
      ‖(1 : K) + z‖ ≤ ‖(1 : K)‖ + ‖z‖ := norm_add_le _ _
      _ = 1 + ‖z‖ := by rw [norm_one]
      _ ≤ 3 / 2 := by linarith
  rw [inversionOddYCoordinateKernel, norm_div, norm_mul, norm_pow]
  rw [div_le_iff₀ (pow_pos (by linarith : 0 < ‖(1 : K) - z‖) 3)]
  nlinarith [norm_nonneg z, hnum, hden3, norm_nonneg ((1 : K) + z)]

/-- The natural-indexed inversion-antisymmetric y-series converges. -/
theorem inversionOddYCoordinateKernel_nat_summable
    {K : Type*} [NormedField K] [CompleteSpace K] {q : K}
    (parameterNorm : ‖q‖ < 1) (u : K) :
    Summable (fun n : ℕ => inversionOddYCoordinateKernel (q ^ n * u)) := by
  have kernelArgumentNormTendsto :
      Filter.Tendsto (fun n : ℕ => ‖q ^ n * u‖) Filter.atTop (nhds 0) := by
    simpa using
      ((tendsto_pow_atTop_nhds_zero_of_norm_lt_one parameterNorm).mul_const u).norm
  have eventuallySmallNorm :
      ∀ᶠ n : ℕ in Filter.atTop, ‖q ^ n * u‖ < 1 / 2 :=
    Filter.Tendsto.eventually_lt_const (by norm_num) kernelArgumentNormTendsto
  have geometricMajorantSummable :
      Summable (fun n : ℕ => (12 * ‖u‖) * ‖q‖ ^ n) :=
    Summable.mul_left (12 * ‖u‖)
      (summable_geometric_of_lt_one (norm_nonneg q) parameterNorm)
  apply geometricMajorantSummable.of_norm_bounded_eventually
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventuallySmallNorm] with n smallNorm
  calc
    ‖inversionOddYCoordinateKernel (q ^ n * u)‖ ≤ 12 * ‖q ^ n * u‖ :=
      inversionOddYCoordinateKernel_norm_le smallNorm.le
    _ = (12 * ‖u‖) * ‖q‖ ^ n := by rw [norm_mul, norm_pow]; ring

/-- The two-sided inversion-antisymmetric y-series converges; its negative half is
the negative of a natural-indexed series by the inversion law, so no large-argument
estimate is needed here. -/
theorem inversionOddYCoordinateKernel_int_summable
    {K : Type*} [NormedField K] [CompleteSpace K] {q : K}
    (parameterNorm : ‖q‖ < 1) (u : K) :
    Summable (fun n : ℤ => inversionOddYCoordinateKernel (q ^ n * u)) := by
  apply summable_int_iff_summable_nat_and_neg.mpr
  refine ⟨?_, ?_⟩
  · simpa only [zpow_natCast] using
      inversionOddYCoordinateKernel_nat_summable parameterNorm u
  · have hf : Summable (fun n : ℕ => inversionOddYCoordinateKernel (q ^ n * u⁻¹)) :=
      inversionOddYCoordinateKernel_nat_summable parameterNorm u⁻¹
    refine (hf.neg).congr (fun n => ?_)
    have hz : q ^ (-(n : ℤ)) * u = (q ^ (n : ℤ) * u⁻¹)⁻¹ := by
      rw [mul_inv_rev, inv_inv, ← zpow_neg, mul_comm]
    rw [hz, inversionOddYCoordinateKernel_inv, zpow_natCast]

/-- The integer-indexed inversion-antisymmetric y-coordinate series. -/
noncomputable def inversionOddYCoordinateSeries {K : Type*} [NormedField K]
    (q u : K) : K :=
  ∑' n : ℤ, inversionOddYCoordinateKernel (q ^ n * u)

/-- `q`-scaling of the parameter leaves the inversion-antisymmetric y-series
unchanged. -/
theorem inversionOddYCoordinateSeries_mul_parameter
    {K : Type*} [NormedField K] {q : K} (parameterNeZero : q ≠ 0) (u : K) :
    inversionOddYCoordinateSeries q (q * u) = inversionOddYCoordinateSeries q u := by
  unfold inversionOddYCoordinateSeries
  calc
    (∑' n : ℤ, inversionOddYCoordinateKernel (q ^ n * (q * u))) =
        ∑' n : ℤ, inversionOddYCoordinateKernel (q ^ (n + 1) * u) := by
      apply tsum_congr
      intro n
      rw [zpow_add₀ parameterNeZero, zpow_one, mul_assoc]
    _ = ∑' n : ℤ, inversionOddYCoordinateKernel (q ^ n * u) :=
      (Equiv.addRight (1 : ℤ)).tsum_eq
        (fun n : ℤ => inversionOddYCoordinateKernel (q ^ n * u))

/-- The inversion-antisymmetric kernel is compatible with ring homomorphisms. -/
theorem inversionOddYCoordinateKernel_map
    {E : Type*} {F : Type*} [Field E] [Field F]
    (fieldHom : E →+* F) (z : E) :
    fieldHom (inversionOddYCoordinateKernel z) =
      inversionOddYCoordinateKernel (fieldHom z) := by
  simp only [inversionOddYCoordinateKernel, map_div₀, map_mul, map_add, map_pow,
    map_sub, map_one]

/-- Naturality of the inversion-antisymmetric y-series in continuous ring
homomorphisms. -/
theorem inversionOddYCoordinateSeries_map
    {E : Type*} {F : Type*} [NormedField E] [CompleteSpace E] [NormedField F]
    (fieldHom : E →+* F) (homContinuous : Continuous fieldHom)
    {q : E} (parameterNorm : ‖q‖ < 1) (u : E) :
    fieldHom (inversionOddYCoordinateSeries q u) =
      inversionOddYCoordinateSeries (fieldHom q) (fieldHom u) := by
  have sourceHasSum :
      HasSum (fun n : ℤ => inversionOddYCoordinateKernel (q ^ n * u))
        (inversionOddYCoordinateSeries q u) :=
    (inversionOddYCoordinateKernel_int_summable parameterNorm u).hasSum
  have transportedHasSum := hasSum_int_map_ringHom fieldHom homContinuous sourceHasSum
  have mappedHasSum :
      HasSum (fun n : ℤ =>
          inversionOddYCoordinateKernel ((fieldHom q) ^ n * fieldHom u))
        (fieldHom (inversionOddYCoordinateSeries q u)) := by
    simpa only [inversionOddYCoordinateKernel_map, map_mul, map_zpow₀]
      using transportedHasSum
  exact mappedHasSum.tsum_eq.symm

end

end LeanFormal.IUT.TateCurve
