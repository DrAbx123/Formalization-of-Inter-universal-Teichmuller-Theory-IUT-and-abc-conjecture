import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceRelativePadicDegrees
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceSelectedPrimePacket

/-!
# The actual relative-degree weights of the selected prime packet

The selected section contracts to the full base prime fiber. Hence each
upper tensor block has dimension Nv times the corresponding base block,
and the reciprocal-Nv weighted dimensions sum to the actual base packet
dimension. This is the arithmetic denominator required by III 3.1.1(ii).
-/

namespace LeanFormal.IUT.NumberFieldFinitePlace

noncomputable section

variable (k K : Type*) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
variable (p : ℕ) [Fact p.Prime] (ι : Type*) [Fintype ι]

abbrev selectedPrimeTupleDegree (tuple : ι → FinitePlaceAtPrime k p) : ℕ :=
  relativeCompletionTupleDegree (k := k) (selectedPrimeArithmeticPlaces k K p ι) tuple

abbrev SelectedPrimeTupleLabels (tuple : ι → FinitePlaceAtPrime k p) :=
  RelativeCompletionTupleLabels (k := k) (selectedPrimeArithmeticPlaces k K p ι) tuple

omit [Fact p.Prime] in
theorem selectedPrimeTupleDegree_pos (tuple : ι → FinitePlaceAtPrime k p) :
    0 < selectedPrimeTupleDegree k K p ι tuple := relativeCompletionTupleDegree_pos _ _

theorem finrank_selectedPrimeArithmeticTensorTupleBlock (tuple : ι → FinitePlaceAtPrime k p) :
    Module.finrank ℚ_[p]
      (ArithmeticTensorTupleBlock (selectedPrimeArithmeticPlaces k K p ι) tuple) =
      selectedPrimeTupleDegree k K p ι tuple *
        Module.finrank ℚ_[p]
          (ArithmeticTensorTupleBlock (fullPrimeArithmeticPlaces k p ι) tuple) := by
  have hdegree := finrank_arithmeticTensorTupleBlock_relative (k := k)
    (selectedPrimeArithmeticPlaces k K p ι) tuple
  have hplaces : (fun i v => relativeCommonPrimePlace (k := k)
      (selectedPrimeArithmeticPlaces k K p ι i v)) = fullPrimeArithmeticPlaces k p ι := by
    funext i v
    exact relativeCommonPrimePlace_selected v
  have hrank := congrArg (fun lowerPlaces : ι → FinitePlaceAtPrime k p → FinitePlaceAtPrime k p =>
    Module.finrank ℚ_[p] (ArithmeticTensorTupleBlock lowerPlaces tuple)) hplaces
  exact hdegree.trans (congrArg (fun d => selectedPrimeTupleDegree k K p ι tuple * d) hrank)

open Classical in
theorem sum_selectedPrimeTupleWeightedDimensions :
    (∑ tuple : ι → FinitePlaceAtPrime k p,
      (1 / (selectedPrimeTupleDegree k K p ι tuple : ℝ)) *
        (Module.finrank ℚ_[p]
          (ArithmeticTensorTupleBlock (selectedPrimeArithmeticPlaces k K p ι) tuple) : ℝ)) =
      (fullPrimeArithmeticTensorDimension k p ι : ℝ) := by
  calc
    _ = ∑ tuple : ι → FinitePlaceAtPrime k p,
        (Module.finrank ℚ_[p]
          (ArithmeticTensorTupleBlock (fullPrimeArithmeticPlaces k p ι) tuple) : ℝ) := by
      apply Finset.sum_congr rfl
      intro tuple _
      rw [finrank_selectedPrimeArithmeticTensorTupleBlock]
      push_cast
      have hdegree : (selectedPrimeTupleDegree k K p ι tuple : ℝ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (selectedPrimeTupleDegree_pos k K p ι tuple).ne'
      field_simp
    _ = _ := by
      exact_mod_cast (fullPrimeArithmeticTensorDimension_eq_sum_tupleBlocks k p ι).symm

end

end LeanFormal.IUT.NumberFieldFinitePlace
