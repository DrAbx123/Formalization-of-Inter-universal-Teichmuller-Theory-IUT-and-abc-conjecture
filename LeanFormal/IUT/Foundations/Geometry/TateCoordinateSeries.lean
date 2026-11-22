import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic

namespace LeanFormal.IUT.TateCurve

/-- The rational kernel used in the Tate coordinate series. -/
def coordinateKernel {K : Type*} [Field K] (z : K) : K :=
  z / (1 - z) ^ 2

theorem coordinateKernel_inv
    {K : Type*} [Field K] (z : K) :
    coordinateKernel z⁻¹ = coordinateKernel z := by
  by_cases argumentZero : z = 0
  · simp [argumentZero, coordinateKernel]
  by_cases argumentOne : z = 1
  · simp [argumentOne, coordinateKernel]
  have denominatorNeZero : 1 - z ≠ 0 := sub_ne_zero.mpr (Ne.symm argumentOne)
  have inverseDifference : 1 - z⁻¹ = (z - 1) / z := by
    field_simp
  unfold coordinateKernel
  rw [inverseDifference, div_pow]
  field_simp [argumentZero, denominatorNeZero, sub_ne_zero.mpr argumentOne]
  ring

/-- The argument avoids every pole of the integer-indexed coordinate series. -/
def coordinatePoleExclusion {K : Type*} [Field K] (q u : K) : Prop :=
  ∀ n : ℤ, q ^ n * u ≠ 1

/-- Nonzero parameters whose entire `q`-orbit avoids the kernel poles. -/
def coordinateParameterDomain {K : Type*} [Field K] (q : K) : Set K :=
  {u | u ≠ 0 ∧ coordinatePoleExclusion q u}

theorem coordinateParameterDomain_mul_parameter_iff
    {K : Type*} [Field K] {q u : K} (parameterNeZero : q ≠ 0) :
    q * u ∈ coordinateParameterDomain q ↔ u ∈ coordinateParameterDomain q := by
  have shiftedArgument (n : ℤ) : q ^ n * (q * u) = q ^ (n + 1) * u := by
    rw [zpow_add₀ parameterNeZero, zpow_one, mul_assoc]
  change (q * u ≠ 0 ∧ coordinatePoleExclusion q (q * u)) ↔
    (u ≠ 0 ∧ coordinatePoleExclusion q u)
  constructor
  · rintro ⟨shiftedArgumentNeZero, shiftedPoleExclusion⟩
    refine ⟨?_, ?_⟩
    · intro argumentZero
      apply shiftedArgumentNeZero
      rw [argumentZero, mul_zero]
    · intro n
      have previousPoleExclusion := shiftedPoleExclusion (n - 1)
      rw [shiftedArgument] at previousPoleExclusion
      simpa only [sub_add_cancel] using previousPoleExclusion
  · rintro ⟨argumentNeZero, poleExclusion⟩
    refine ⟨mul_ne_zero parameterNeZero argumentNeZero, ?_⟩
    intro n
    rw [shiftedArgument]
    exact poleExclusion (n + 1)

theorem coordinatePoleExclusion_denominator_ne_zero
    {K : Type*} [Field K] {q u : K}
    (poleExclusion : coordinatePoleExclusion q u) (n : ℤ) :
    (1 - q ^ n * u) ^ 2 ≠ 0 := by
  exact pow_ne_zero 2 (sub_ne_zero.mpr (poleExclusion n).symm)

theorem coordinateKernel_norm_le
    {K : Type*} [NormedField K] {z : K} (smallNorm : ‖z‖ ≤ 1 / 2) :
    ‖coordinateKernel z‖ ≤ 4 * ‖z‖ := by
  have denominatorLowerBound : (1 / 2 : ℝ) ≤ ‖(1 : K) - z‖ := by
    have normDifferenceBound := norm_sub_norm_le (1 : K) z
    rw [norm_one] at normDifferenceBound
    linarith
  have denominatorSquareLowerBound : (1 / 4 : ℝ) ≤ ‖(1 : K) - z‖ ^ 2 := by
    nlinarith
  rw [coordinateKernel, norm_div, norm_pow]
  apply (div_le_iff₀ (by linarith : 0 < ‖(1 : K) - z‖ ^ 2)).2
  nlinarith [norm_nonneg z]

theorem coordinateKernel_nat_summable
    {K : Type*} [NormedField K] [CompleteSpace K] {q : K}
    (parameterNorm : ‖q‖ < 1) (u : K) :
    Summable (fun n : ℕ => coordinateKernel (q ^ n * u)) := by
  have kernelArgumentNormTendsto :
      Filter.Tendsto (fun n : ℕ => ‖q ^ n * u‖) Filter.atTop (nhds 0) := by
    simpa using
      ((tendsto_pow_atTop_nhds_zero_of_norm_lt_one parameterNorm).mul_const u).norm
  have eventuallySmallNorm :
      ∀ᶠ n : ℕ in Filter.atTop, ‖q ^ n * u‖ < 1 / 2 :=
    Filter.Tendsto.eventually_lt_const (by norm_num) kernelArgumentNormTendsto
  have geometricMajorantSummable :
      Summable (fun n : ℕ => (4 * ‖u‖) * ‖q‖ ^ n) :=
    Summable.mul_left (4 * ‖u‖)
      (summable_geometric_of_lt_one (norm_nonneg q) parameterNorm)
  apply geometricMajorantSummable.of_norm_bounded_eventually
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventuallySmallNorm] with n smallNorm
  calc
    ‖coordinateKernel (q ^ n * u)‖ ≤ 4 * ‖q ^ n * u‖ :=
      coordinateKernel_norm_le smallNorm.le
    _ = (4 * ‖u‖) * ‖q‖ ^ n := by rw [norm_mul, norm_pow]; ring

theorem coordinateKernel_int_summable
    {K : Type*} [NormedField K] [CompleteSpace K] {q : K}
    (parameterNorm : ‖q‖ < 1) (u : K) :
    Summable (fun n : ℤ => coordinateKernel (q ^ n * u)) := by
  apply summable_int_iff_summable_nat_and_neg.mpr
  constructor
  · simpa only [zpow_natCast] using coordinateKernel_nat_summable parameterNorm u
  · apply (coordinateKernel_nat_summable parameterNorm u⁻¹).congr
    intro n
    rw [← coordinateKernel_inv (q ^ (-(n : ℤ)) * u)]
    simp only [mul_inv_rev, zpow_neg, zpow_natCast, inv_inv]
    rw [mul_comm]

/-- The integer-indexed kernel sum, using Lean's total definition of `tsum`. -/
noncomputable def coordinateSeries {K : Type*} [NormedField K] (q u : K) : K :=
  ∑' n : ℤ, coordinateKernel (q ^ n * u)

theorem coordinateSeries_mul_parameter
    {K : Type*} [NormedField K] {q : K} (parameterNeZero : q ≠ 0) (u : K) :
    coordinateSeries q (q * u) = coordinateSeries q u := by
  unfold coordinateSeries
  calc
    (∑' n : ℤ, coordinateKernel (q ^ n * (q * u))) =
        ∑' n : ℤ, coordinateKernel (q ^ (n + 1) * u) := by
      apply tsum_congr
      intro n
      rw [zpow_add₀ parameterNeZero, zpow_one, mul_assoc]
    _ = ∑' n : ℤ, coordinateKernel (q ^ n * u) :=
      (Equiv.addRight (1 : ℤ)).tsum_eq (fun n : ℤ => coordinateKernel (q ^ n * u))

theorem coordinateKernel_map
    {E : Type*} {F : Type*} [Field E] [Field F]
    (fieldHom : E →+* F) (z : E) :
    fieldHom (coordinateKernel z) = coordinateKernel (fieldHom z) := by
  simp only [coordinateKernel, map_div₀, map_pow, map_sub, map_one]

theorem hasSum_int_map_ringHom
    {E : Type*} {F : Type*} [NormedField E] [NormedField F]
    (fieldHom : E →+* F) (homContinuous : Continuous fieldHom)
    {summand : ℤ → E} {seriesValue : E} (sourceHasSum : HasSum summand seriesValue) :
    HasSum (fun n : ℤ => fieldHom (summand n)) (fieldHom seriesValue) := by
  exact sourceHasSum.map fieldHom homContinuous

theorem coordinateSeries_map
    {E : Type*} {F : Type*} [NormedField E] [CompleteSpace E] [NormedField F]
    (fieldHom : E →+* F) (homContinuous : Continuous fieldHom)
    {q : E} (parameterNorm : ‖q‖ < 1) (u : E) :
    fieldHom (coordinateSeries q u) = coordinateSeries (fieldHom q) (fieldHom u) := by
  have sourceHasSum :
      HasSum (fun n : ℤ => coordinateKernel (q ^ n * u)) (coordinateSeries q u) :=
    (coordinateKernel_int_summable parameterNorm u).hasSum
  have transportedHasSum := hasSum_int_map_ringHom fieldHom homContinuous sourceHasSum
  have mappedHasSum :
      HasSum (fun n : ℤ => coordinateKernel ((fieldHom q) ^ n * fieldHom u))
        (fieldHom (coordinateSeries q u)) := by
    simpa only [coordinateKernel_map, map_mul, map_zpow₀] using transportedHasSum
  exact mappedHasSum.tsum_eq.symm

end LeanFormal.IUT.TateCurve
