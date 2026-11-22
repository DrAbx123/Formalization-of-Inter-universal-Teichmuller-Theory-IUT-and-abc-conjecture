import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceSelectedPrimeWeights
import LeanFormal.IUT.Foundations.MeasureTheory.FiniteWeightedProductLogVolume
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicHaarScaling

/-!
# The selected arithmetic packet's actual weighted relative log-volume

The labels have the actual relative tensor degrees Nv, and each component
measure is Haar measure on the actual upper tuple tensor. Dividing the
constructed E-weighted relative logarithm by the actual base packet
dimension gives coefficients 1/(Nv*Dbase). A reference region is explicit;
this file does not identify arbitrary references with an integral unit region.
-/

namespace LeanFormal.IUT.NumberFieldFinitePlace

open MeasureTheory LeanFormal.IUT.FiniteWeightedProduct
open LeanFormal.IUT.FinitePadicHaarScaling
open scoped Pointwise

noncomputable section

variable (k K : Type*) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
variable (p : ℕ) [Fact p.Prime] (ι : Type*) [Fintype ι]

abbrev SelectedPrimeTupleBlock (tuple : ι → FinitePlaceAtPrime k p) :=
  ArithmeticTensorTupleBlock (selectedPrimeArithmeticPlaces k K p ι) tuple

variable [∀ tuple, MeasurableSpace (SelectedPrimeTupleBlock k K p ι tuple)]
variable [∀ tuple, BorelSpace (SelectedPrimeTupleBlock k K p ι tuple)]

open Classical in
def selectedPrimeWeightedRelativeLogVolume
    (S C : Set ((tuple : ι → FinitePlaceAtPrime k p) →
      SelectedPrimeTupleBlock k K p ι tuple)) : ℝ :=
  weightedRelativeLogVolume (SelectedPrimeTupleLabels k K p ι)
    (SelectedPrimeTupleBlock k K p ι) (fun _ => Measure.addHaar) S C /
      (fullPrimeArithmeticTensorDimension k p ι : ℝ)

open Classical in
theorem selectedPrimeWeightedRelativeLogVolume_pi
    (S C : (tuple : ι → FinitePlaceAtPrime k p) → Set (SelectedPrimeTupleBlock k K p ι tuple))
    (hSpos : ∀ tuple, 0 < Measure.addHaar (S tuple))
    (hSfin : ∀ tuple, Measure.addHaar (S tuple) < ⊤)
    (hCpos : ∀ tuple, 0 < Measure.addHaar (C tuple))
    (hCfin : ∀ tuple, Measure.addHaar (C tuple) < ⊤) :
    selectedPrimeWeightedRelativeLogVolume k K p ι (Set.pi Set.univ S) (Set.pi Set.univ C) =
      ∑ tuple, (1 / ((selectedPrimeTupleDegree k K p ι tuple : ℝ) *
        (fullPrimeArithmeticTensorDimension k p ι : ℝ))) *
          (Real.log (Measure.addHaar (S tuple)).toReal -
            Real.log (Measure.addHaar (C tuple)).toReal) := by
  unfold selectedPrimeWeightedRelativeLogVolume
  rw [weightedRelativeLogVolume_pi _ _ _ S C hSpos hSfin hCpos hCfin, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro tuple _
  simp only [SelectedPrimeTupleLabels, RelativeCompletionTupleLabels, Fintype.card_fin,
    div_eq_mul_inv, mul_inv_rev]
  ring

theorem selectedPrimeTupleHaar_prime_smul_pos_lt_top
    (tuple : ι → FinitePlaceAtPrime k p) {S : Set (SelectedPrimeTupleBlock k K p ι tuple)}
    (hpos : 0 < Measure.addHaar S) (hfin : Measure.addHaar S < ⊤) :
    0 < Measure.addHaar ((p : ℚ_[p]) • S) ∧ Measure.addHaar ((p : ℚ_[p]) • S) < ⊤ := by
  rw [measure_prime_smul_finiteDimensional]
  have hp : (p : ENNReal) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime p).ne_zero
  have hfactor : 0 < ((p : ENNReal) ^ Module.finrank ℚ_[p]
      (SelectedPrimeTupleBlock k K p ι tuple))⁻¹ ∧
      ((p : ENNReal) ^ Module.finrank ℚ_[p] (SelectedPrimeTupleBlock k K p ι tuple))⁻¹ < ⊤ := by
    exact ⟨ENNReal.inv_pos.mpr (ENNReal.pow_ne_top (ENNReal.natCast_ne_top p)),
      ENNReal.inv_lt_top.mpr (pos_iff_ne_zero.mpr (pow_ne_zero _ hp))⟩
  exact ⟨ENNReal.mul_pos hfactor.1.ne' hpos.ne', ENNReal.mul_lt_top hfactor.2 hfin⟩

open Classical in
theorem selectedPrimeWeightedRelativeLogVolume_mul_prime
    (S C : (tuple : ι → FinitePlaceAtPrime k p) → Set (SelectedPrimeTupleBlock k K p ι tuple))
    (hSpos : ∀ tuple, 0 < Measure.addHaar (S tuple))
    (hSfin : ∀ tuple, Measure.addHaar (S tuple) < ⊤)
    (hCpos : ∀ tuple, 0 < Measure.addHaar (C tuple))
    (hCfin : ∀ tuple, Measure.addHaar (C tuple) < ⊤) :
    selectedPrimeWeightedRelativeLogVolume k K p ι
      (Set.pi Set.univ (fun tuple => (p : ℚ_[p]) • S tuple)) (Set.pi Set.univ C) =
      -Real.log (p : ℝ) +
        selectedPrimeWeightedRelativeLogVolume k K p ι (Set.pi Set.univ S) (Set.pi Set.univ C) := by
  have hscaled tuple := selectedPrimeTupleHaar_prime_smul_pos_lt_top k K p ι tuple
    (hSpos tuple) (hSfin tuple)
  have hlog tuple := log_measure_prime_smul_finiteDimensional (p := p) Measure.addHaar
    (hSpos tuple) (hSfin tuple)
  unfold selectedPrimeWeightedRelativeLogVolume
  rw [weightedRelativeLogVolume_pi _ _ _ _ C (fun tuple => (hscaled tuple).1)
    (fun tuple => (hscaled tuple).2) hCpos hCfin,
    weightedRelativeLogVolume_pi _ _ _ S C hSpos hSfin hCpos hCfin]
  simp only [SelectedPrimeTupleLabels, RelativeCompletionTupleLabels, Fintype.card_fin]
  simp_rw [hlog]
  have hsum :
      (∑ tuple, (1 / (selectedPrimeTupleDegree k K p ι tuple : ℝ)) *
        (-(Module.finrank ℚ_[p] (SelectedPrimeTupleBlock k K p ι tuple) : ℝ) * Real.log (p : ℝ) +
          Real.log (Measure.addHaar (S tuple)).toReal -
            Real.log (Measure.addHaar (C tuple)).toReal)) =
      -Real.log (p : ℝ) * (fullPrimeArithmeticTensorDimension k p ι : ℝ) +
        ∑ tuple, (1 / (selectedPrimeTupleDegree k K p ι tuple : ℝ)) *
          (Real.log (Measure.addHaar (S tuple)).toReal -
            Real.log (Measure.addHaar (C tuple)).toReal) := by
    rw [← sum_selectedPrimeTupleWeightedDimensions k K p ι, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro tuple _
    ring
  rw [hsum]
  have hbase : (fullPrimeArithmeticTensorDimension k p ι : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (fullPrimeArithmeticTensorDimension_pos k p ι).ne'
  field_simp

end

end LeanFormal.IUT.NumberFieldFinitePlace
