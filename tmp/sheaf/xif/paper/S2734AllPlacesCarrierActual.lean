import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPrimeSupport
import LeanFormal.IUT.ABCBridge.Geometry.FreyTateAnalyticInput
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

noncomputable section
open scoped BigOperators
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2734AllPlacesCarrierActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace

/-- The all-places carrier: one completion factor for every finite place of ℚ. -/
abbrev AllPlacesCarrier : Type :=
  (v : NumberField.FinitePlace ℚ) → NumberFieldFinitePlace.Completion v

/-- The rational point embedded in every finite-place completion. -/
def allPlacesPoint (x : ℚ) : AllPlacesCarrier :=
  fun v => algebraMap ℚ (NumberFieldFinitePlace.Completion v) x

@[simp] theorem allPlacesPoint_apply (x : ℚ) (v : NumberField.FinitePlace ℚ) :
    allPlacesPoint x v =
      algebraMap ℚ (NumberFieldFinitePlace.Completion v) x := rfl

/-- The finite-support p-adic product norm attached to a rational point: product
of the actual `padicNorm` at the primes in the arithmetic prime support. -/
noncomputable def allPlacesSupportNorm (x : ℚ) : Real :=
  ∏ p in arithmeticPrimeSupport x, (padicNorm p x : Real)

/-- The negative log of the product norm is the sum of the negative local
log-norms over the prime support. -/
theorem neg_log_allPlacesSupportNorm_eq_sum {x : ℚ}
    (hpos : ∀ p ∈ arithmeticPrimeSupport x, 0 < (padicNorm p x : Real)) :
    -Real.log (allPlacesSupportNorm x) =
      ∑ p in arithmeticPrimeSupport x,
        -Real.log (padicNorm p x : Real) := by
  unfold allPlacesSupportNorm
  rw [Real.log_prod]
  · rw [Finset.sum_neg_distrib]
  · intro p hp
    exact ne_of_gt (hpos p hp)

/-- The local negative log is valuation-weighted: `-log padicNorm p x = v_p(x) log p`
for nonzero `x`.  This is the actual local formula behind the product norm. -/
theorem neg_log_padicNorm_eq_valuation {p : Nat} [Fact p.Prime] {x : ℚ}
    (hx : x ≠ 0) :
    -Real.log (padicNorm p x : Real) =
      (padicValRat p x : Real) * Real.log (p : Real) := by
  rw [← Real.log_inv]
  congr 1
  rw [padicNorm.eq_zpow_of_nonzero hx]
  rw [← zpow_neg]
  rw [show ((p : ℚ) : Real) = (p : Real) by norm_num]
  rw [Real.rpow_neg (by positivity), Real.rpow_intCast]
  rw [inv_inv]

/-- Exact structural mismatch: the product norm log is the valuation-weighted
sum over the point support, while `arithmeticWeight` is the unweighted sum of
`log p` over the union support of the three coordinates `a, c-a, c`.  These
differ already at `x = 4` (left `2 log 2`, right `log 2`). -/
def AllPlacesNormWeightMismatch : Prop :=
  ∀ x : ℚ, x ≠ 0 →
    -Real.log (allPlacesSupportNorm x) =
      ∑ p in arithmeticPrimeSupport x,
        (padicValRat p x : Real) * Real.log (p : Real)

theorem allPlacesNormWeightMismatch_of :
    AllPlacesNormWeightMismatch :=
  fun x hx => by
    rw [neg_log_allPlacesSupportNorm_eq_sum]
    · apply Finset.sum_congr rfl
      intro p hp
      exact neg_log_padicNorm_eq_valuation (p := p) hx
    · intro p hp
      have hp' : Nat.Prime p := prime_of_mem_arithmeticPrimeSupport hp
      haveI : Fact (Nat.Prime p) := ⟨hp'⟩
      exact_mod_cast padicNorm_pos (p := p) hx

#check AllPlacesCarrier
#check allPlacesPoint
#check allPlacesSupportNorm
#check neg_log_allPlacesSupportNorm_eq_sum
#check neg_log_padicNorm_eq_valuation
#check AllPlacesNormWeightMismatch
#print axioms allPlacesNormWeightMismatch_of

end LeanFormal.IUT.XiFPaper.S2734AllPlacesCarrierActual
end
