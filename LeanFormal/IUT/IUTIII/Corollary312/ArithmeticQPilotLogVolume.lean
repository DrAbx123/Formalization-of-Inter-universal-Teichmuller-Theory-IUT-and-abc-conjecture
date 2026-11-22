import LeanFormal.IUT.Foundations.NumberField.LocalQParameter
import LeanFormal.IUT.Foundations.Arithmetic.NormLog

/-!
Arithmetic q-pilot logarithms at selected number-field finite places.

The input is an actual local completion element satisfying the q-candidate
conditions. No elliptic Tate uniformization or identification of normalization
weights with the IUT paper is asserted by this file.
-/

namespace LeanFormal.IUT

namespace ArithmeticQPilotLogVolume

open NumberFieldFinitePlace

universe u

variable {K : Type u} [Field K] [NumberField K]

variable {place : NumberField.FinitePlace K}

/-- The standard number-field completion norm of a q-candidate is positive. -/
theorem qNorm_pos (parameter : FinitePlaceQCandidate place) :
    0 < ‖parameter.q‖ :=
  norm_pos_iff.mpr parameter.q_ne_zero

/-- The candidate's discrete valuation inequality implies the norm inequality. -/
theorem qNorm_lt_one (parameter : FinitePlaceQCandidate place) :
    ‖parameter.q‖ < 1 := by
  exact Valued.toNormedField.norm_lt_one_iff.mpr parameter.valuation_lt_one

/-- The local signed q-logarithm, computed from the actual completion element. -/
noncomputable def localSignedLog (parameter : FinitePlaceQCandidate place) : ℝ :=
  Real.log ‖parameter.q‖

/-- The positive local logarithmic magnitude of the actual completion element. -/
noncomputable def localLogMagnitude (parameter : FinitePlaceQCandidate place) : ℝ :=
  -localSignedLog parameter

theorem localSignedLog_neg (parameter : FinitePlaceQCandidate place) :
    localSignedLog parameter < 0 :=
  Real.log_neg (qNorm_pos parameter) (qNorm_lt_one parameter)

theorem localLogMagnitude_pos (parameter : FinitePlaceQCandidate place) :
    0 < localLogMagnitude parameter :=
  neg_pos.mpr (localSignedLog_neg parameter)

theorem localSignedLog_eq_neg_magnitude (parameter : FinitePlaceQCandidate place) :
    localSignedLog parameter = -localLogMagnitude parameter := by
  simp [localLogMagnitude]

theorem abs_localSignedLog (parameter : FinitePlaceQCandidate place) :
    |localSignedLog parameter| = localLogMagnitude parameter :=
  abs_of_neg (localSignedLog_neg parameter)

/-- Compatibility with the existing norm/log degree, without a second degree map. -/
theorem unitNormLogDegree_q (parameter : FinitePlaceQCandidate place) :
    Multiplicative.toAdd
        (unitNormLogDegree (Completion place)
          (Units.mk0 parameter.q parameter.q_ne_zero)) =
      localSignedLog parameter :=
  rfl

theorem exp_neg_localLogMagnitude (parameter : FinitePlaceQCandidate place) :
    Real.exp (-localLogMagnitude parameter) = ‖parameter.q‖ := by
  simp only [localLogMagnitude, localSignedLog, neg_neg]
  exact Real.exp_log (qNorm_pos parameter)

/-- Positive powers multiply the local magnitude by their natural exponent. -/
theorem localLogMagnitude_pow (parameter : FinitePlaceQCandidate place)
    (exponent : ℕ) (exponent_pos : 0 < exponent) :
    localLogMagnitude (parameter.pow exponent exponent_pos) =
      (exponent : ℝ) * localLogMagnitude parameter := by
  simp only [localLogMagnitude, localSignedLog, FinitePlaceQCandidate.pow_q,
    norm_pow, Real.log_pow, mul_neg]

section SelectedPlaces

variable (selectedPlaces : Finset (NumberField.FinitePlace K))
  (parameters : (selectedPlace : selectedPlaces) → FinitePlaceQCandidate selectedPlace.val)
  (weights : selectedPlaces → ℝ)

/-!
The following finite aggregation is conditional on the supplied weights. It
does not construct arithmetic local degrees, identify the selected places
with all bad-reduction places, or identify these sums with the paper's
normalized q-pilot volume.
-/

/-- A finite weighted sum of local magnitudes on exactly the selected places. -/
noncomputable def selectedLogMagnitude : ℝ :=
  ∑ selectedPlace : selectedPlaces,
    weights selectedPlace * localLogMagnitude (parameters selectedPlace)

/-- The signed finite sum with the same parameters and exactly the same weights. -/
noncomputable def selectedSignedLog : ℝ :=
  ∑ selectedPlace : selectedPlaces,
    weights selectedPlace * localSignedLog (parameters selectedPlace)

theorem selectedSignedLog_eq_neg_magnitude :
    selectedSignedLog selectedPlaces parameters weights =
      -selectedLogMagnitude selectedPlaces parameters weights := by
  simp only [selectedSignedLog, selectedLogMagnitude,
    localSignedLog_eq_neg_magnitude, mul_neg, Finset.sum_neg_distrib]

theorem selectedLogMagnitude_pos
    (selectedPlaces_nonempty : selectedPlaces.Nonempty)
    (weights_pos : ∀ selectedPlace, 0 < weights selectedPlace) :
    0 < selectedLogMagnitude selectedPlaces parameters weights := by
  unfold selectedLogMagnitude
  apply Finset.sum_pos
  · intro selectedPlace _
    exact mul_pos (weights_pos selectedPlace)
      (localLogMagnitude_pos (parameters selectedPlace))
  · obtain ⟨selectedPlace, selectedPlace_mem⟩ := selectedPlaces_nonempty
    exact ⟨⟨selectedPlace, selectedPlace_mem⟩, Finset.mem_univ _⟩

theorem selectedSignedLog_neg
    (selectedPlaces_nonempty : selectedPlaces.Nonempty)
    (weights_pos : ∀ selectedPlace, 0 < weights selectedPlace) :
    selectedSignedLog selectedPlaces parameters weights < 0 := by
  rw [selectedSignedLog_eq_neg_magnitude]
  exact neg_neg_of_pos
    (selectedLogMagnitude_pos selectedPlaces parameters weights
      selectedPlaces_nonempty weights_pos)

theorem abs_selectedSignedLog
    (selectedPlaces_nonempty : selectedPlaces.Nonempty)
    (weights_pos : ∀ selectedPlace, 0 < weights selectedPlace) :
    |selectedSignedLog selectedPlaces parameters weights| =
      selectedLogMagnitude selectedPlaces parameters weights := by
  rw [abs_of_neg (selectedSignedLog_neg selectedPlaces parameters weights
    selectedPlaces_nonempty weights_pos), selectedSignedLog_eq_neg_magnitude, neg_neg]

end SelectedPlaces

end ArithmeticQPilotLogVolume

end LeanFormal.IUT
