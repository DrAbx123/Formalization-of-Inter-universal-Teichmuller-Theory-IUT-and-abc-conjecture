import LeanFormal.IUT.IUTII.Frobenioid.ConcreteSourceFrobenioidBridge
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionNormTransport
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnits
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedCompletion

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000

/-!
# Normalized norm vs the actual valuation unit ball (L0.4)

Scratch.  For the actual completion
`K = concretePlace.maximalIdeal.adicCompletion GaussianField`, the tree proves the
canonical log-norm formula

  `Real.log ‖x‖ = nu(x) * Real.log absNorm`   (`norm_eq_absNorm_zpow`),

where `nu(x)` is the integer valuation exponent of `Valued.v`.  Because
`absNorm > 1`, this gives the exact identification of the norm unit ball with
the valuation integer ring:

  `‖x‖ ≤ 1 ↔ Valued.v x ≤ 1`  and  `‖x‖ < 1 ↔ Valued.v x < 1`.

This is precisely the comparison needed to identify the principal units of the
norm unit ball (`LeanFormal.IUT.LocalFieldIntegralUnits.principalUnits`) with
the principal units of the actual valuation ring.  The production principal-unit
exponent theorem can then be applied to the integral unit produced by
`UniformizerDVRDecomposition`.  No card, no wrapper; actual canonical formula only.
-/

noncomputable section

namespace LeanFormal.IUT.NormalizedLogNormComparison

open scoped WithZero Valued
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ConcreteSourceFrobenioidBridge
open LeanFormal.IUT.LocalFieldIntegralUnits

universe u

local instance gaussianNormalizedLogNormIrreducibleFact :
    Fact (Irreducible
      (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨LeanFormal.IUT.gaussianPolynomial_irreducible⟩

/-- The actual completed valuation field at the concrete Gaussian place. -/
abbrev completionField : Type :=
  concretePlace.maximalIdeal.adicCompletion GaussianField

abbrev valuedInteger : Subring completionField :=
  (Valued.v : Valuation completionField (WithZero (Multiplicative ℤ))).integer

theorem absNorm_gt_one :
    (1 : ℝ) < (Ideal.absNorm concretePlace.maximalIdeal.asIdeal : ℝ) :=
  by
  exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm
    concretePlace.maximalIdeal)

theorem valued_ne_zero_of_ne_zero {x : completionField} (hx : x ≠ 0) :
    (Valued.v x : WithZero (Multiplicative ℤ)) ≠ 0 :=
  fun h => hx ((Valued.v).map_eq_zero_iff.mp h)

/-- Log-norm comparison: `‖x‖ ≤ 1` iff the actual valuation is integral. -/
theorem norm_le_one_iff_valued_le_one (x : completionField) :
    ‖x‖ ≤ 1 ↔ (Valued.v x : WithZero (Multiplicative ℤ)) ≤ 1 := by
  by_cases hx : x = 0
  · subst x
    simp
  · let ν : ℤ := Multiplicative.toAdd (WithZero.unzero (valued_ne_zero_of_ne_zero hx))
    have hv : (Valued.v x : WithZero (Multiplicative ℤ)) =
        WithZero.exp ν := by
      dsimp [ν]
      exact (WithZero.coe_unzero (valued_ne_zero_of_ne_zero hx)).symm
    have hbase := absNorm_gt_one
    have hnorm : ‖x‖ =
        (Ideal.absNorm concretePlace.maximalIdeal.asIdeal : ℝ) ^ ν := by
      dsimp [ν]
      exact norm_eq_absNorm_zpow concretePlace x hx
    rw [hnorm, zpow_le_one_iff_right₀ hbase]
    rw [hv, show (1 : WithZero (Multiplicative ℤ)) = WithZero.exp (0 : ℤ) from
      WithZero.exp_zero.symm]
    rw [WithZero.exp_le_exp]

/-- Strict form: `‖x‖ < 1` iff the actual valuation is integral but not a unit. -/
theorem norm_lt_one_iff_valued_lt_one (x : completionField) :
    ‖x‖ < 1 ↔ (Valued.v x : WithZero (Multiplicative ℤ)) < 1 := by
  by_cases hx : x = 0
  · subst x
    simp
  · let ν : ℤ := Multiplicative.toAdd (WithZero.unzero (valued_ne_zero_of_ne_zero hx))
    have hv : (Valued.v x : WithZero (Multiplicative ℤ)) =
        WithZero.exp ν := by
      dsimp [ν]
      exact (WithZero.coe_unzero (valued_ne_zero_of_ne_zero hx)).symm
    have hbase := absNorm_gt_one
    have hnorm : ‖x‖ =
        (Ideal.absNorm concretePlace.maximalIdeal.asIdeal : ℝ) ^ ν := by
      dsimp [ν]
      exact norm_eq_absNorm_zpow concretePlace x hx
    rw [hnorm, zpow_lt_one_iff_right₀ hbase]
    rw [hv, show (1 : WithZero (Multiplicative ℤ)) = WithZero.exp (0 : ℤ) from
      WithZero.exp_zero.symm]
    rw [WithZero.exp_lt_exp]

/-- The norm unit ball is exactly the actual valuation integer ring. -/
theorem norm_integer_eq_valued_integer :
    (LocalFieldIntegralUnits.Integers completionField : Subring completionField) =
      valuedInteger := by
  ext x
  rw [LocalFieldIntegralUnits.mem_integers_iff, Valuation.mem_integer_iff]
  exact norm_le_one_iff_valued_le_one x

/-- The norm-one sphere is exactly the unit group of the actual valuation ring. -/
theorem norm_one_iff_valued_one {x : completionField} (_hx : x ≠ 0) :
    ‖x‖ = 1 ↔ (Valued.v x : WithZero (Multiplicative ℤ)) = 1 := by
  constructor
  · intro hnorm
    have hle : (Valued.v x : WithZero (Multiplicative ℤ)) ≤ 1 := by
      exact (norm_le_one_iff_valued_le_one x).mp hnorm.le
    have hnotlt : ¬ (Valued.v x : WithZero (Multiplicative ℤ)) < 1 := by
      intro hlt
      have hnormlt : ‖x‖ < 1 := (norm_lt_one_iff_valued_lt_one x).mpr hlt
      linarith
    exact le_antisymm hle (le_of_not_gt hnotlt)
  · intro hv
    have hle : ‖x‖ ≤ 1 := (norm_le_one_iff_valued_le_one x).mpr hv.le
    have hnotlt : ¬ ‖x‖ < 1 := by
      intro hlt
      have hvlt : (Valued.v x : WithZero (Multiplicative ℤ)) < 1 :=
        (norm_lt_one_iff_valued_lt_one x).mp hlt
      rw [hv] at hvlt
      exact lt_irrefl _ hvlt
    exact le_antisymm hle (le_of_not_gt hnotlt)


end LeanFormal.IUT.NormalizedLogNormComparison

end
