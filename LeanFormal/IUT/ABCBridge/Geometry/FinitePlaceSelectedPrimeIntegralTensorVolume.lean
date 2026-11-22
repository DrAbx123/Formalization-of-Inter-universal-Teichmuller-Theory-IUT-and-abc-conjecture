import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIntegralTensorCovolume
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceSelectedPrimeWeightedHullVolume

/-!
# Actual selected weighted integral log-tensor volumes

The monoanalytic integral structure is the actual Zp tensor lattice.
Its signed unit-relative volume is computed by the proved finite
intersection indices. Actual relative degrees Nv and the base packet
dimension supply the weights, and each lattice is contained in the
existing canonical holomorphic hull.
-/

namespace LeanFormal.IUT.NumberFieldFinitePlace

open LeanFormal.IUT.LocalFieldProductHull MeasureTheory
open scoped Pointwise

noncomputable section

universe u v w

variable (k : Type u) (K : Type v) [Field k] [NumberField k] [Field K] [NumberField K]
variable [Algebra k K] (p : ℕ) [Fact p.Prime] (ι : Type w) [Fintype ι]

def selectedPrimeIntegralLogTensorGrid :
    Set ((tuple : ι → FinitePlaceAtPrime k p) → SelectedPrimeTupleBlock k K p ι tuple) :=
  Set.pi Set.univ (fun tuple => (arithmeticTupleIntegralLogLattice
    (selectedPrimeArithmeticPlaces k K p ι) tuple : Set (SelectedPrimeTupleBlock k K p ι tuple)))

open Classical in
def selectedPrimeWeightedIntegralTensorLogVolume : ℝ :=
  (∑ tuple : ι → FinitePlaceAtPrime k p,
    (1 / (selectedPrimeTupleDegree k K p ι tuple : ℝ)) *
      arithmeticTupleLogTensorUnitLogVolume (selectedPrimeArithmeticPlaces k K p ι) tuple) /
        (fullPrimeArithmeticTensorDimension k p ι : ℝ)

section ActualHaar

variable [∀ tuple, MeasurableSpace (SelectedPrimeTupleBlock k K p ι tuple)]
variable [∀ tuple, BorelSpace (SelectedPrimeTupleBlock k K p ι tuple)]

theorem selectedPrimeWeightedIntegralTensorLogVolume_eq_relativeLogVolume :
    selectedPrimeWeightedIntegralTensorLogVolume k K p ι =
      selectedPrimeWeightedRelativeLogVolume k K p ι
        (selectedPrimeIntegralLogTensorGrid k K p ι)
        (selectedPrimeCanonicalUnitReferenceGrid k K p ι) := by
  classical
  have hlattice tuple := measure_arithmeticTupleIntegralLogLattice_pos_lt_top
    (selectedPrimeArithmeticPlaces k K p ι) tuple Measure.addHaar
  have hreference tuple := (measure_arithmeticTupleCanonicalRegions_pos_lt_top
    (selectedPrimeArithmeticPlaces k K p ι) tuple Measure.addHaar).2
  symm
  unfold selectedPrimeIntegralLogTensorGrid selectedPrimeCanonicalUnitReferenceGrid
  rw [selectedPrimeWeightedRelativeLogVolume_pi _ _ _ _ _ _
    (fun tuple => (hlattice tuple).1) (fun tuple => (hlattice tuple).2)
    (fun tuple => (hreference tuple).1) (fun tuple => (hreference tuple).2)]
  unfold selectedPrimeWeightedIntegralTensorLogVolume
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro tuple _
  rw [arithmeticTupleLogTensorUnitLogVolume_eq_relativeHaarLog _ _ Measure.addHaar]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem selectedPrimeWeightedIntegralTensorLogVolume_mul_prime :
    selectedPrimeWeightedRelativeLogVolume k K p ι
      (Set.pi Set.univ (fun tuple => (p : ℚ_[p]) •
        (arithmeticTupleIntegralLogLattice (selectedPrimeArithmeticPlaces k K p ι) tuple :
          Set (SelectedPrimeTupleBlock k K p ι tuple))))
      (selectedPrimeCanonicalUnitReferenceGrid k K p ι) =
      -Real.log (p : ℝ) + selectedPrimeWeightedIntegralTensorLogVolume k K p ι := by
  have hlattice tuple := measure_arithmeticTupleIntegralLogLattice_pos_lt_top
    (selectedPrimeArithmeticPlaces k K p ι) tuple Measure.addHaar
  have hreference tuple := (measure_arithmeticTupleCanonicalRegions_pos_lt_top
    (selectedPrimeArithmeticPlaces k K p ι) tuple Measure.addHaar).2
  have hscale := selectedPrimeWeightedRelativeLogVolume_mul_prime k K p ι
    (fun tuple => (arithmeticTupleIntegralLogLattice (selectedPrimeArithmeticPlaces k K p ι)
      tuple : Set (SelectedPrimeTupleBlock k K p ι tuple)))
    (arithmeticTupleCanonicalUnitReference (selectedPrimeArithmeticPlaces k K p ι))
    (fun tuple => (hlattice tuple).1) (fun tuple => (hlattice tuple).2)
    (fun tuple => (hreference tuple).1) (fun tuple => (hreference tuple).2)
  rw [selectedPrimeWeightedIntegralTensorLogVolume_eq_relativeLogVolume k K p ι]
  exact hscale

end ActualHaar

theorem selectedPrimeWeightedIntegralTensorLogVolume_le_hull :
    selectedPrimeWeightedIntegralTensorLogVolume k K p ι ≤
      selectedPrimeWeightedHullLogVolume k K p ι := by
  classical
  letI : ∀ tuple, MeasurableSpace (SelectedPrimeTupleBlock k K p ι tuple) := fun _ => borel _
  letI : ∀ tuple, BorelSpace (SelectedPrimeTupleBlock k K p ι tuple) := fun _ => ⟨rfl⟩
  unfold selectedPrimeWeightedIntegralTensorLogVolume selectedPrimeWeightedHullLogVolume
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro tuple _
  exact mul_le_mul_of_nonneg_left
    (arithmeticTupleLogTensorUnitLogVolume_le_hull
      (selectedPrimeArithmeticPlaces k K p ι) tuple Measure.addHaar) (by positivity)

variable {J : (ι → FinitePlaceAtPrime k p) → Type (max v w)} [∀ tuple, Finite (J tuple)]
variable {E : (tuple : ι → FinitePlaceAtPrime k p) → J tuple → Type (max v w)}
variable [∀ tuple j, NormedField (E tuple j)] [∀ tuple j, NormedAlgebra ℚ_[p] (E tuple j)]
variable [∀ tuple j, FiniteDimensional ℚ_[p] (E tuple j)] [∀ tuple j, ProperSpace (E tuple j)]

open Classical in
theorem selectedPrimeWeightedIntegralTensorLogVolume_eq_fieldProducts
    (e : ∀ tuple, SelectedPrimeTupleBlock k K p ι tuple ≃ₐ[ℚ_[p]] ((j : J tuple) → E tuple j)) :
    selectedPrimeWeightedIntegralTensorLogVolume k K p ι =
      (∑ tuple, (1 / (selectedPrimeTupleDegree k K p ι tuple : ℝ)) *
        (letI : MeasurableSpace ((j : J tuple) → E tuple j) := borel _
         letI : BorelSpace ((j : J tuple) → E tuple j) := ⟨rfl⟩
         normalizedLogVolume Measure.addHaar
           (e tuple '' (arithmeticTupleIntegralLogLattice
             (selectedPrimeArithmeticPlaces k K p ι) tuple :
               Set (SelectedPrimeTupleBlock k K p ι tuple))))) /
                 (fullPrimeArithmeticTensorDimension k p ι : ℝ) := by
  letI : ∀ tuple, MeasurableSpace (SelectedPrimeTupleBlock k K p ι tuple) := fun _ => borel _
  letI : ∀ tuple, BorelSpace (SelectedPrimeTupleBlock k K p ι tuple) := fun _ => ⟨rfl⟩
  unfold selectedPrimeWeightedIntegralTensorLogVolume
  congr 1
  apply Finset.sum_congr rfl
  intro tuple _
  letI : MeasurableSpace ((j : J tuple) → E tuple j) := borel _
  letI : BorelSpace ((j : J tuple) → E tuple j) := ⟨rfl⟩
  rw [arithmeticTupleLogTensorUnitLogVolume_eq_fieldLogVolume _ _ (e tuple)
    Measure.addHaar Measure.addHaar]

open Classical in
theorem selectedPrimeWeightedIntegralTensorLogVolume_eq_fieldFunctional
    (e : ∀ tuple, SelectedPrimeTupleBlock k K p ι tuple ≃ₐ[ℚ_[p]] ((j : J tuple) → E tuple j)) :
    letI : ∀ tuple, MeasurableSpace ((j : J tuple) → E tuple j) := fun _ => borel _
    letI : ∀ tuple, BorelSpace ((j : J tuple) → E tuple j) := fun _ => ⟨rfl⟩
    selectedPrimeWeightedIntegralTensorLogVolume k K p ι =
      FiniteWeightedProduct.weightedRelativeLogVolume (SelectedPrimeTupleLabels k K p ι)
        (fun tuple => (j : J tuple) → E tuple j) (fun _ => Measure.addHaar)
        (Set.pi Set.univ (fun tuple => e tuple '' (arithmeticTupleIntegralLogLattice
          (selectedPrimeArithmeticPlaces k K p ι) tuple :
            Set (SelectedPrimeTupleBlock k K p ι tuple))))
        (Set.pi Set.univ (fun tuple => unitRegion (K := E tuple))) /
          (fullPrimeArithmeticTensorDimension k p ι : ℝ) := by
  letI : ∀ tuple, MeasurableSpace ((j : J tuple) → E tuple j) := fun _ => borel _
  letI : ∀ tuple, BorelSpace ((j : J tuple) → E tuple j) := fun _ => ⟨rfl⟩
  have hmass tuple :
      0 < Measure.addHaar (e tuple '' (arithmeticTupleIntegralLogLattice
        (selectedPrimeArithmeticPlaces k K p ι) tuple :
          Set (SelectedPrimeTupleBlock k K p ι tuple))) ∧
      Measure.addHaar (e tuple '' (arithmeticTupleIntegralLogLattice
        (selectedPrimeArithmeticPlaces k K p ι) tuple :
          Set (SelectedPrimeTupleBlock k K p ι tuple))) < ⊤ := by
    let homeomorphism := (e tuple).toLinearEquiv.toContinuousLinearEquiv.toHomeomorph
    have hopen := homeomorphism.isOpenMap _
      (isOpen_arithmeticTupleIntegralLogLattice (selectedPrimeArithmeticPlaces k K p ι) tuple)
    have hcompact := (isCompact_arithmeticTupleIntegralLogLattice
      (selectedPrimeArithmeticPlaces k K p ι) tuple).image homeomorphism.continuous
    change IsOpen (e tuple '' (arithmeticTupleIntegralLogLattice
      (selectedPrimeArithmeticPlaces k K p ι) tuple :
        Set (SelectedPrimeTupleBlock k K p ι tuple))) at hopen
    exact ⟨Measure.measure_pos_of_nonempty_interior Measure.addHaar (by
      rw [hopen.interior_eq]
      exact ⟨e tuple 0, ⟨0, Submodule.zero_mem _, rfl⟩⟩), hcompact.measure_lt_top⟩
  have hunit tuple := measure_unitRegion_pos_lt_top
    (Measure.addHaar : Measure ((j : J tuple) → E tuple j))
  rw [FiniteWeightedProduct.weightedRelativeLogVolume_pi _ _ _ _ _
    (fun tuple => (hmass tuple).1) (fun tuple => (hmass tuple).2)
    (fun tuple => (hunit tuple).1) (fun tuple => (hunit tuple).2)]
  simpa only [SelectedPrimeTupleLabels, RelativeCompletionTupleLabels, Fintype.card_fin,
    normalizedLogVolume] using
      selectedPrimeWeightedIntegralTensorLogVolume_eq_fieldProducts k K p ι e

end

end LeanFormal.IUT.NumberFieldFinitePlace
