import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedCompletion
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnits

/-!
# The actual integer ring is unchanged by normalization

Continuity of a field homomorphism forces it to preserve the closed unit
ball: scale bounded powers into a small neighborhood of zero, then use
unboundedness of real powers greater than one. Apply this in both directions
to the proved homeomorphism between the two norms on the actual K_v.
This identifies actual completed valuation integers with normalized integers.
-/

namespace LeanFormal.IUT.LocalFieldLogarithm

open Filter
open scoped Topology

/-- A continuous map of normed fields preserves norm-integral elements.
No norm-isometry hypothesis is needed. -/
theorem norm_map_le_one_of_continuous {F E : Type*} [NontriviallyNormedField F]
    [NormedField E] (e : F →+* E) (he : Continuous e) {x : F} (hx : ‖x‖ ≤ 1) :
    ‖e x‖ ≤ 1 := by
  obtain ⟨δ, hδ, hmap⟩ := Metric.continuousAt_iff.mp
    (he.continuousAt : ContinuousAt e (0 : F)) 1 (by norm_num)
  obtain ⟨a, ha, haδ⟩ := NormedField.exists_norm_lt F hδ
  have hea : 0 < ‖e a‖ := norm_pos_iff.mpr
    (fun h => (norm_pos_iff.mp ha) (e.injective (by simpa only [map_zero] using h)))
  have hbound : ∀ n : ℕ, ‖e x‖ ^ n < 1 / ‖e a‖ := by
    intro n
    have hsmall : ‖e (a * x ^ n)‖ < 1 := by
      have hinput : dist (a * x ^ n) 0 < δ := by
        rw [dist_zero_right, norm_mul, norm_pow]
        exact (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hx)).trans_lt haδ
      simpa only [map_zero, dist_zero_right] using hmap hinput
    rw [map_mul, map_pow, norm_mul, norm_pow] at hsmall
    exact (lt_div_iff₀ hea).mpr (by simpa only [mul_comm] using hsmall)
  by_contra hle
  have hlarge := (tendsto_pow_atTop_atTop_of_one_lt (lt_of_not_ge hle)).eventually
    (eventually_gt_atTop (1 / ‖e a‖))
  obtain ⟨n, hn⟩ := hlarge.exists
  exact (hbound n).not_gt hn

end LeanFormal.IUT.LocalFieldLogarithm

namespace LeanFormal.IUT.NumberFieldFinitePlace

open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.LocalFieldLogarithm
open scoped Valued

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/-- Equality of the two actual integer balls, without claiming equality
of the numerical norms. -/
theorem normalizedCompletion_norm_le_one_iff (place : NumberField.FinitePlace K)
    (x : NormalizedCompletion place) :
    ‖normalizedCompletionRingEquiv place x‖ ≤ 1 ↔ ‖x‖ ≤ 1 := by
  constructor
  · intro hx
    have h := norm_map_le_one_of_continuous (normalizedCompletionRingEquiv place).symm.toRingHom
      (normalizedCompletionHomeomorph place).symm.continuous hx
    simpa using h
  · exact norm_map_le_one_of_continuous (normalizedCompletionRingEquiv place).toRingHom
      (normalizedCompletionHomeomorph place).continuous

theorem mem_completionIntegers_iff_norm_le_one (place : NumberField.FinitePlace K)
    (x : Completion place) : x ∈ CompletionIntegers place ↔ ‖x‖ ≤ 1 := by
  change (Valued.v x : WithZero (Multiplicative ℤ)) ≤ 1 ↔ ‖x‖ ≤ 1
  exact Valued.toNormedField.norm_le_one_iff.symm

/-- The maximal-ideal balls agree as well: apply the closed-unit-ball
comparison to inverses and complement the resulting inequality. -/
theorem normalizedCompletion_norm_lt_one_iff (place : NumberField.FinitePlace K)
    (x : NormalizedCompletion place) :
    ‖normalizedCompletionRingEquiv place x‖ < 1 ↔ ‖x‖ < 1 := by
  by_cases hx : x = 0
  · subst x
    simp
  have hnew : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hold : 0 < ‖normalizedCompletionRingEquiv place x‖ :=
    norm_pos_iff.mpr (fun h => hx ((normalizedCompletionRingEquiv place).injective
      (by simpa only [map_zero] using h)))
  have hinv := normalizedCompletion_norm_le_one_iff place x⁻¹
  rw [map_inv₀, norm_inv, norm_inv, inv_le_one₀ hold, inv_le_one₀ hnew] at hinv
  simpa only [not_le] using not_congr hinv

/-- The actual completed integer ring, identified with the integer ring
for the normalized norm on the same completed field. -/
def normalizedCompletionIntegersEquiv (place : NumberField.FinitePlace K) :
    Integers (NormalizedCompletion place) ≃+* CompletionIntegers place where
  toFun x := ⟨normalizedCompletionRingEquiv place x,
    (mem_completionIntegers_iff_norm_le_one place _).mpr
      ((normalizedCompletion_norm_le_one_iff place _).mpr x.property)⟩
  invFun x := ⟨(normalizedCompletionRingEquiv place).symm x,
    (normalizedCompletion_norm_le_one_iff place _).mp (by
      simpa using (mem_completionIntegers_iff_norm_le_one place _).mp x.property)⟩
  left_inv x := Subtype.ext ((normalizedCompletionRingEquiv place).symm_apply_apply x)
  right_inv x := Subtype.ext ((normalizedCompletionRingEquiv place).apply_symm_apply x)
  map_mul' x y := Subtype.ext ((normalizedCompletionRingEquiv place).map_mul x y)
  map_add' x y := Subtype.ext ((normalizedCompletionRingEquiv place).map_add x y)

def normalizedCompletionIntegersHomeomorph (place : NumberField.FinitePlace K) :
    Integers (NormalizedCompletion place) ≃ₜ CompletionIntegers place where
  toEquiv := (normalizedCompletionIntegersEquiv place).toEquiv
  continuous_toFun :=
    ((normalizedCompletionHomeomorph place).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((normalizedCompletionHomeomorph place).symm.continuous.comp
      continuous_subtype_val).subtype_mk _

end

end LeanFormal.IUT.NumberFieldFinitePlace
