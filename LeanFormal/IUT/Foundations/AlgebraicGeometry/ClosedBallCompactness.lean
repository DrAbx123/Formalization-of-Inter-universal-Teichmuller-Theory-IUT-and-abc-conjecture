import LeanFormal.IUT.Foundations.AlgebraicGeometry.NormalizedLogNormComparison
import LeanFormal.IUT.Foundations.AlgebraicGeometry.UniformizerDVRDecomposition
import LeanFormal.IUT.ABCBridge.Geometry.AdicCompletionValuationUniqueness
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionLocalInputs
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Topology.Algebra.Order.Archimedean

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

/-!
# Closed-ball compactness for the canonical completion (L0.4 A/C batch)

Goal: derive `ProperSpace` for

  `K = concretePlace.maximalIdeal.adicCompletion GaussianField`

from the actual compact valuation integer ring, without using a spectral-norm
or `NormedSpace ℚ_[5]` instance.

The argument is self-contained in the canonical completion norm:

1. the closed unit ball is the compact valuation integer ring
   (`closedBall_zero_one_eq_valuedInteger`);
2. the actual uniformizer `π` has `‖π‖ < 1`;
3. scaling by a nonzero `a` sends the unit ball to the ball of radius `‖a‖`
   (`closedBall_mul_eq_of_nonneg`);
4. the balls `‖π‖^{-n}` grow without bound, and every ball of radius `r` is
   contained in one of them; a closed subset of a compact set is compact;
5. translating by `x` gives compactness of every `closedBall x r`;
6. `ProperSpace K` follows.

This constructs the actual closed-ball compactness; it does not require the
missing `NormedSpace ℚ_[5]` instance from `CanonicalCompletionNormedSpace`.

No fake instance, no card, no production edits.
-/

noncomputable section

namespace LeanFormal.IUT.ClosedBallCompactness

open scoped WithZero Valued
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ConcreteSourceFrobenioidBridge
open LeanFormal.IUT.NormalizedLogNormComparison
open LeanFormal.IUT.UniformizerDVRDecomposition

universe u

local instance gaussianClosedBallIrreducibleFact :
    Fact (Irreducible
      (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨LeanFormal.IUT.gaussianPolynomial_irreducible⟩

/-- The canonical completed valuation field at the concrete Gaussian place. -/
abbrev completionField : Type :=
  LeanFormal.IUT.NormalizedLogNormComparison.completionField

/-- The actual uniformizer of the canonical completion. -/
noncomputable abbrev uniformizer : completionField :=
  LeanFormal.IUT.UniformizerDVRDecomposition.concreteAdicUniformizer

/-! ## The uniformizer has norm strictly below one -/

theorem uniformizer_valued_lt_one :
    (Valued.v uniformizer : WithZero (Multiplicative ℤ)) < 1 := by
  dsimp [uniformizer]
  rw [LeanFormal.IUT.UniformizerDVRDecomposition.concreteAdicUniformizer_valued]
  exact LeanFormal.IUT.NumberFieldFinitePlace.withZero_exp_neg_one_lt_one

theorem uniformizer_norm_lt_one : ‖uniformizer‖ < 1 :=
  (norm_lt_one_iff_valued_lt_one uniformizer).mpr uniformizer_valued_lt_one

theorem uniformizer_norm_pos : 0 < ‖uniformizer‖ :=
  norm_pos_iff.mpr (LeanFormal.IUT.UniformizerDVRDecomposition.concreteAdicUniformizer_ne_zero)

/-! ## The unit ball is compact -/

/-- The actual valuation integer ring is compact, directly from the production
`compactSpace_adicCompletionIntegers` theorem. -/
theorem compactSpace_valuedInteger : CompactSpace valuedInteger := by
  change CompactSpace
    (concretePlace.maximalIdeal.adicCompletionIntegers GaussianField)
  exact LeanFormal.IUT.NumberFieldFinitePlace.compactSpace_adicCompletionIntegers
    (k := GaussianField) concretePlace

/-- The closed unit ball is exactly the valuation integer ring. -/
theorem closedBall_zero_one_eq_valuedInteger :
    Metric.closedBall (0 : completionField) 1 = (valuedInteger : Set completionField) := by
  ext x
  rw [Metric.mem_closedBall, dist_zero_right]
  exact norm_le_one_iff_valued_le_one x

/-- The closed unit ball is compact. -/
theorem isCompact_closedBall_zero_one :
    IsCompact (Metric.closedBall (0 : completionField) 1) := by
  rw [closedBall_zero_one_eq_valuedInteger]
  exact isCompact_iff_compactSpace.mpr compactSpace_valuedInteger

/-! ## Scaling closed balls by multiplication -/

theorem closedBall_mul_eq_of_nonneg
    (a : completionField) (ha : a ≠ 0) (r : ℝ) (hr : 0 ≤ r) :
    (fun y : completionField => a * y) ''
        Metric.closedBall (0 : completionField) r =
      Metric.closedBall (0 : completionField) (‖a‖ * r) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Metric.mem_closedBall] at hy ⊢
    rw [dist_zero_right] at hy
    rw [dist_zero_right, norm_mul]
    exact mul_le_mul_of_nonneg_left hy (norm_nonneg a)
  · intro hx
    refine ⟨a⁻¹ * x, ?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right, norm_mul, norm_inv]
      have hx' : ‖x‖ ≤ ‖a‖ * r := by
        simpa [dist_zero_right] using hx
      calc ‖a‖⁻¹ * ‖x‖ ≤ ‖a‖⁻¹ * (‖a‖ * r) :=
          mul_le_mul_of_nonneg_left hx' (inv_nonneg.mpr (norm_nonneg a))
        _ = r := by field_simp [ha]
    · field_simp [ha]

theorem isCompact_mul_closedBall_one (a : completionField) (ha : a ≠ 0) :
    IsCompact ((fun y : completionField => a * y) ''
      Metric.closedBall (0 : completionField) 1) := by
  have hcont : Continuous fun x : completionField => a * x :=
    continuous_const.mul continuous_id
  exact isCompact_closedBall_zero_one.image hcont

theorem closedBall_zero_of_norm_eq (a : completionField) (ha : a ≠ 0) :
    Metric.closedBall (0 : completionField) ‖a‖ =
      (fun y : completionField => a * y) ''
        Metric.closedBall (0 : completionField) 1 := by
  rw [closedBall_mul_eq_of_nonneg a ha 1 zero_le_one, mul_one]

theorem isCompact_closedBall_zero_norm_pow_inv (n : ℕ) :
    IsCompact (Metric.closedBall (0 : completionField)
      (‖uniformizer‖⁻¹ ^ n)) := by
  have hnonzero : (uniformizer ^ n) ≠ 0 :=
    pow_ne_zero n (LeanFormal.IUT.UniformizerDVRDecomposition.concreteAdicUniformizer_ne_zero)
  have hnorm : (‖uniformizer ^ n‖) = ‖uniformizer‖ ^ n := by
    rw [norm_pow]
  have hrewrite : (‖uniformizer‖⁻¹ ^ n) = ‖(uniformizer ^ n)⁻¹‖ := by
    rw [norm_inv, hnorm, inv_pow]
  rw [hrewrite]
  have h := isCompact_mul_closedBall_one (uniformizer ^ n)⁻¹ (inv_ne_zero hnonzero)
  rw [closedBall_zero_of_norm_eq ((uniformizer ^ n)⁻¹) (inv_ne_zero hnonzero)] at h
  exact h

/-! ## Every radius is bounded by a compact normalized ball -/

theorem exists_nat_radius_ge (r : ℝ) (hr : 0 ≤ r) :
    ∃ n : ℕ, r ≤ ‖uniformizer‖⁻¹ ^ n := by
  have hpos : 0 < ‖uniformizer‖ := uniformizer_norm_pos
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ‖uniformizer‖ ^ n < (r + 1)⁻¹ :=
    exists_pow_lt_of_lt_one (by positivity) uniformizer_norm_lt_one
  refine ⟨n, ?_⟩
  have hpowpos : 0 < ‖uniformizer‖ ^ n := pow_pos hpos n
  have hinv : r + 1 < (‖uniformizer‖ ^ n)⁻¹ := by
    exact (lt_inv_comm₀ (by positivity) hpowpos).mpr hn
  have hpowinv : (‖uniformizer‖⁻¹) ^ n = (‖uniformizer‖ ^ n)⁻¹ := by
    rw [inv_pow]
  rw [hpowinv]
  linarith

theorem isCompact_closedBall_zero (r : ℝ) :
    IsCompact (Metric.closedBall (0 : completionField) r) := by
  rcases lt_or_ge r 0 with hr | hr
  · rw [Metric.closedBall_eq_empty.mpr hr]
    exact isCompact_empty
  · obtain ⟨n, hn⟩ := exists_nat_radius_ge r hr
    have hcompact : IsCompact (Metric.closedBall (0 : completionField)
        (‖uniformizer‖⁻¹ ^ n)) :=
      isCompact_closedBall_zero_norm_pow_inv n
    exact hcompact.of_isClosed_subset Metric.isClosed_closedBall
      (Metric.closedBall_subset_closedBall hn)

/-! ## Translation and properness -/

theorem isCompact_closedBall (x : completionField) (r : ℝ) :
    IsCompact (Metric.closedBall x r) := by
  have hcont : Continuous fun y : completionField => x + y :=
    continuous_const.add continuous_id
  have himage : (fun y : completionField => x + y) ''
      Metric.closedBall (0 : completionField) r = Metric.closedBall x r := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [Metric.mem_closedBall] at hy ⊢
      rw [dist_eq_norm]
      simpa using hy
    · intro hz
      refine ⟨z - x, ?_, ?_⟩
      · rw [Metric.mem_closedBall, dist_eq_norm]
        have hz' : ‖z - x‖ ≤ r := by
          simpa [dist_eq_norm] using hz
        simpa [norm_sub_rev] using hz'
      · ring
  rw [← himage]
  exact (isCompact_closedBall_zero r).image hcont

/-- **Closed-ball compactness.** The canonical completion is proper, derived
without any spectral-norm or `NormedSpace ℚ_[5]` instance. -/
theorem properSpaceCanonicalCompletion : ProperSpace completionField :=
  ⟨fun x r => isCompact_closedBall x r⟩

/-! ## Consumers of the properness theorem -/

/-- The canonical completion is a proper normed field; this is the exact
topological input needed by the production uniform principal-unit theorem. -/
theorem properSpaceCanonicalCompletion_consumer :
    ProperSpace completionField :=
  properSpaceCanonicalCompletion

/-- Under the derived properness, the actual norm integral unit group is
compact. -/
theorem compactSpace_integralUnits : CompactSpace
    (LeanFormal.IUT.LocalFieldIntegralUnits.Integers completionField)ˣ := by
  letI : ProperSpace completionField := properSpaceCanonicalCompletion
  exact LeanFormal.IUT.LocalFieldIntegralUnits.compactSpace_units
    (K := completionField)

/-- The production uniform principal-unit exponent theorem applies to the
canonical completion with the properness proved in this file. -/
theorem exists_uniform_principalUnit_exponent_canonical :
    ∃ N : ℕ, 0 < N ∧
      ∀ u : (LeanFormal.IUT.LocalFieldIntegralUnits.Integers
        completionField)ˣ,
        u ^ N ∈ LeanFormal.IUT.LocalFieldIntegralUnits.principalUnits := by
  letI : ProperSpace completionField := properSpaceCanonicalCompletion
  exact LeanFormal.IUT.LocalFieldIntegralUnits.exists_uniform_principalUnit_exponent
    (K := completionField)

/-! ## Closed-ball compactness and the unit sphere -/

/-- Every unit sphere is compact in the canonical completion. -/
theorem isCompact_sphere (x : completionField) (r : ℝ) :
    IsCompact (Metric.sphere x r) :=
  (isCompact_closedBall x r).of_isClosed_subset Metric.isClosed_sphere
    Metric.sphere_subset_closedBall

/-- Every closed ball is a compact space when regarded as a subtype. -/
theorem compactSpace_closedBall_subtype (x : completionField) (r : ℝ) :
    CompactSpace (Metric.closedBall x r) :=
  isCompact_iff_compactSpace.mp (isCompact_closedBall x r)

/-- The actual integral unit ball is compact after translating the unit-ball
identification; this is the valuation-unit version of `compactSpace_units`. -/
theorem compactSpace_integralUnits_canonical : CompactSpace
    (LeanFormal.IUT.LocalFieldIntegralUnits.Integers completionField)ˣ :=
  compactSpace_integralUnits

end LeanFormal.IUT.ClosedBallCompactness

end