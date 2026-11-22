import LeanFormal.IUT.Foundations.NumberField.LocalQParameterRamification
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotLogVolume

/-!
The arithmetic normalization of q-logarithms under finite-place extension.

Mathlib's canonical completion norm has base the absolute norm of the
maximal ideal. Consequently an actual completion embedding scales the
q-logarithmic magnitude by the ramification index times the residue degree.
Dividing instead by the logarithm of the residue norm recovers the discrete
order, which scales by the ramification index alone.

These are arithmetic identities for the existing q-candidates. They do not
prove Tate uniformization or construct the paper's global q-pilot weights.
-/

namespace LeanFormal.IUT

namespace ArithmeticQPilotBaseChange

open NumberFieldFinitePlace ArithmeticQPilotLogVolume

universe u v

noncomputable section

section SinglePlace

variable {K : Type u} [Field K] [NumberField K]

/-- The arithmetic base used by Mathlib's canonical completion norm. -/
def residueNormBase (place : NumberField.FinitePlace K) : ℝ :=
  Ideal.absNorm place.maximalIdeal.asIdeal

theorem residueNormBase_gt_one (place : NumberField.FinitePlace K) :
    1 < residueNormBase place := by
  unfold residueNormBase
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm place.maximalIdeal

theorem log_residueNormBase_pos (place : NumberField.FinitePlace K) :
    0 < Real.log (residueNormBase place) :=
  Real.log_pos (residueNormBase_gt_one place)

variable {place : NumberField.FinitePlace K}

/-- The norm formula uses the actual arithmetic residue norm, not a chosen base. -/
theorem qNorm_eq_residueNormBase_zpow
    (parameter : FinitePlaceQCandidate place) :
    ‖parameter.q‖ = residueNormBase place ^ (-parameter.exponent) := by
  rw [NumberField.FinitePlace.norm_def (underlyingPrime place),
    WithZeroMulInt.toNNReal_neg_apply _ parameter.valuation_ne_zero,
    NNReal.coe_zpow]
  simp [residueNormBase, NumberFieldFinitePlace.underlyingPrime,
    FinitePlaceQCandidate.exponent]

theorem localLogMagnitude_eq_exponent_mul_log
    (parameter : FinitePlaceQCandidate place) :
    localLogMagnitude parameter =
      (parameter.exponent : ℝ) * Real.log (residueNormBase place) := by
  unfold localLogMagnitude localSignedLog
  rw [qNorm_eq_residueNormBase_zpow, Real.log_zpow]
  simp only [Int.cast_neg, neg_mul, neg_neg]

theorem qOrder_cast_eq_exponent_cast
    (parameter : FinitePlaceQCandidate place) :
    (parameter.order : ℝ) = (parameter.exponent : ℝ) := by
  have integer_order : (parameter.order : ℤ) = parameter.exponent :=
    Int.toNat_of_nonneg (le_of_lt parameter.exponent_pos)
  exact_mod_cast integer_order

theorem localLogMagnitude_eq_order_mul_log
    (parameter : FinitePlaceQCandidate place) :
    localLogMagnitude parameter =
      (parameter.order : ℝ) * Real.log (residueNormBase place) := by
  rw [qOrder_cast_eq_exponent_cast, localLogMagnitude_eq_exponent_mul_log]

/-- Normalization by the residue logarithm recovers the discrete local order.
This is not asserted to be the global normalization of the IUT paper. -/
def orderNormalizedMagnitude (parameter : FinitePlaceQCandidate place) : ℝ :=
  localLogMagnitude parameter / Real.log (residueNormBase place)

theorem orderNormalizedMagnitude_eq_order
    (parameter : FinitePlaceQCandidate place) :
    orderNormalizedMagnitude parameter = (parameter.order : ℝ) := by
  unfold orderNormalizedMagnitude
  rw [localLogMagnitude_eq_order_mul_log]
  exact mul_div_cancel_right₀ _ (ne_of_gt (log_residueNormBase_pos place))

theorem orderNormalizedMagnitude_pos
    (parameter : FinitePlaceQCandidate place) :
    0 < orderNormalizedMagnitude parameter := by
  rw [orderNormalizedMagnitude_eq_order]
  exact_mod_cast parameter.order_pos

/-- The q-candidate record has no additional data beyond its actual element. -/
theorem qCandidate_eq_of_element_eq
    (leftParameter rightParameter : FinitePlaceQCandidate place)
    (element_eq : leftParameter.q = rightParameter.q) :
    leftParameter = rightParameter := by
  cases leftParameter
  cases rightParameter
  cases element_eq
  rfl

end SinglePlace

section PlaceExtension

variable {k : Type u} {K : Type v}
  [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

/-- The ramification index of the actual contracted and upper finite places. -/
def localRamificationIndex (place : NumberField.FinitePlace K) : ℕ :=
  (comap (k := k) place).maximalIdeal.asIdeal.ramificationIdx'
    place.maximalIdeal.asIdeal

/-- The residue degree of the actual contracted and upper finite places. -/
def localResidueDegree (place : NumberField.FinitePlace K) : ℕ :=
  (comap (k := k) place).maximalIdeal.asIdeal.inertiaDeg'
    place.maximalIdeal.asIdeal

/-- The exponent relating the canonical completion norms is the product `e f`. -/
def completionNormDegree (place : NumberField.FinitePlace K) : ℕ :=
  localRamificationIndex (k := k) place * localResidueDegree (k := k) place

theorem residueNormBase_eq_lower_pow (place : NumberField.FinitePlace K) :
    residueNormBase place =
      residueNormBase (comap (k := k) place) ^ localResidueDegree (k := k) place := by
  have residue_cardinality :=
    Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver
      place.maximalIdeal.asIdeal (comap (k := k) place).maximalIdeal.asIdeal
      (comap (k := k) place).maximalIdeal.isPrime
      (comap (k := k) place).maximalIdeal.ne_bot
  unfold residueNormBase localResidueDegree
  exact_mod_cast residue_cardinality

theorem localResidueDegree_pos (place : NumberField.FinitePlace K) :
    0 < localResidueDegree (k := k) place := by
  apply Nat.pos_of_ne_zero
  intro residue_degree_zero
  have residue_base_eq := residueNormBase_eq_lower_pow (k := k) place
  rw [residue_degree_zero, pow_zero] at residue_base_eq
  exact (ne_of_gt (residueNormBase_gt_one place)) residue_base_eq

theorem completionNormDegree_pos (place : NumberField.FinitePlace K) :
    0 < completionNormDegree (k := k) place :=
  Nat.mul_pos (Nat.pos_of_ne_zero (ramificationIdx_ne_zero (k := k) place))
    (localResidueDegree_pos (k := k) place)

theorem log_residueNormBase_eq_residueDegree_mul
    (place : NumberField.FinitePlace K) :
    Real.log (residueNormBase place) =
      (localResidueDegree (k := k) place : ℝ) *
        Real.log (residueNormBase (comap (k := k) place)) := by
  rw [residueNormBase_eq_lower_pow (k := k), Real.log_pow]

variable (place : NumberField.FinitePlace K)
  (parameter : FinitePlaceQCandidate (comap (k := k) place))

/-- Actual completion transport commutes with positive integral powers. -/
theorem mappedPositivePower (power : ℕ) (power_pos : 0 < power) :
    FinitePlaceQCandidate.map place (parameter.pow power power_pos) =
      (FinitePlaceQCandidate.map place parameter).pow power power_pos := by
  apply qCandidate_eq_of_element_eq
  simp only [FinitePlaceQCandidate.map_q, FinitePlaceQCandidate.pow_q, map_pow]

/-- The unnormalized logarithmic magnitude scales by `e f`, not merely `e`. -/
theorem localLogMagnitude_map :
    localLogMagnitude (FinitePlaceQCandidate.map place parameter) =
      (completionNormDegree (k := k) place : ℝ) * localLogMagnitude parameter := by
  simp only [localLogMagnitude_eq_order_mul_log]
  rw [FinitePlaceQCandidate.order_map,
    log_residueNormBase_eq_residueDegree_mul (k := k) place]
  dsimp [completionNormDegree, localRamificationIndex, localResidueDegree]
  push_cast
  ring

theorem localSignedLog_map :
    localSignedLog (FinitePlaceQCandidate.map place parameter) =
      (completionNormDegree (k := k) place : ℝ) * localSignedLog parameter := by
  rw [localSignedLog_eq_neg_magnitude, localLogMagnitude_map,
    localSignedLog_eq_neg_magnitude, mul_neg]

/-- This norm identity is derived from the arithmetic logarithmic scaling. -/
theorem qNorm_map :
    ‖(FinitePlaceQCandidate.map place parameter).q‖ =
      ‖parameter.q‖ ^ completionNormDegree (k := k) place := by
  have magnitude_eq :
      localLogMagnitude (FinitePlaceQCandidate.map place parameter) =
        localLogMagnitude
          (parameter.pow (completionNormDegree (k := k) place)
            (completionNormDegree_pos (k := k) place)) := by
    rw [localLogMagnitude_map, localLogMagnitude_pow]
  have norm_eq := congrArg (fun magnitude : ℝ => Real.exp (-magnitude)) magnitude_eq
  rw [exp_neg_localLogMagnitude, exp_neg_localLogMagnitude] at norm_eq
  simpa only [FinitePlaceQCandidate.pow_q, norm_pow] using norm_eq

/-- Dividing by the actual residue logarithm removes the residue-degree factor. -/
theorem orderNormalizedMagnitude_map :
    orderNormalizedMagnitude (FinitePlaceQCandidate.map place parameter) =
      (localRamificationIndex (k := k) place : ℝ) *
        orderNormalizedMagnitude parameter := by
  simpa only [orderNormalizedMagnitude_eq_order, Nat.cast_mul,
    localRamificationIndex] using
    congrArg (fun order : ℕ => (order : ℝ))
      (FinitePlaceQCandidate.order_map (k := k) place parameter)

theorem localLogMagnitude_map_pow (power : ℕ) (power_pos : 0 < power) :
    localLogMagnitude
        (FinitePlaceQCandidate.map place (parameter.pow power power_pos)) =
      ((completionNormDegree (k := k) place * power : ℕ) : ℝ) *
        localLogMagnitude parameter := by
  rw [localLogMagnitude_map, localLogMagnitude_pow, Nat.cast_mul]
  ring

theorem localSignedLog_map_pow (power : ℕ) (power_pos : 0 < power) :
    localSignedLog
        (FinitePlaceQCandidate.map place (parameter.pow power power_pos)) =
      ((completionNormDegree (k := k) place * power : ℕ) : ℝ) *
        localSignedLog parameter := by
  rw [localSignedLog_eq_neg_magnitude, localLogMagnitude_map_pow,
    localSignedLog_eq_neg_magnitude, mul_neg]

section SelectedUpperPlaces

variable (selectedUpperPlaces : Finset (NumberField.FinitePlace K))
  (parameters : (selectedPlace : selectedUpperPlaces) →
    FinitePlaceQCandidate (comap (k := k) selectedPlace.val))
  (weights : selectedUpperPlaces → ℝ)

/-- The exact finite sum after actual completion transport. The right-hand sum
retains the upper-place index, so distinct upper places above one lower place
are not silently identified or counted only once. No global weights are chosen. -/
theorem selectedLogMagnitude_map :
    selectedLogMagnitude selectedUpperPlaces
        (fun selectedPlace =>
          FinitePlaceQCandidate.map selectedPlace.val (parameters selectedPlace)) weights =
      ∑ selectedPlace : selectedUpperPlaces,
        (weights selectedPlace *
            (completionNormDegree (k := k) selectedPlace.val : ℝ)) *
          localLogMagnitude (parameters selectedPlace) := by
  unfold selectedLogMagnitude
  apply Finset.sum_congr rfl
  intro selectedPlace _
  rw [localLogMagnitude_map]
  ring

end SelectedUpperPlaces

end PlaceExtension

end

end ArithmeticQPilotBaseChange

end LeanFormal.IUT
