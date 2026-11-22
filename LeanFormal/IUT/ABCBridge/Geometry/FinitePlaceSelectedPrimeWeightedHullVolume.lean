import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTupleCanonicalHull
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTensorBlockHull
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceSelectedPrimeWeightedVolume

/-!
# The actual selected log-shell hull's canonical weighted log-volume

The regions and their unit references are the proved decomposition-independent
sets on the actual tuple tensors. The E-weighted Haar construction evaluates
their Cartesian product with the actual relative degrees and base dimension.
The final set identity connects this product to the actual global field hull.
-/

namespace LeanFormal.IUT.NumberFieldFinitePlace

open LeanFormal.IUT.LocalFieldProductHull MeasureTheory
open scoped Pointwise

noncomputable section

universe u v w

variable (k : Type u) (K : Type v) [Field k] [NumberField k] [Field K] [NumberField K]
variable [Algebra k K] (p : ℕ) [Fact p.Prime] (ι : Type w) [Fintype ι]

def selectedPrimeCanonicalHullGrid :
    Set ((tuple : ι → FinitePlaceAtPrime k p) → SelectedPrimeTupleBlock k K p ι tuple) :=
  Set.pi Set.univ (arithmeticTupleCanonicalHull (selectedPrimeArithmeticPlaces k K p ι))

def selectedPrimeCanonicalUnitReferenceGrid :
    Set ((tuple : ι → FinitePlaceAtPrime k p) → SelectedPrimeTupleBlock k K p ι tuple) :=
  Set.pi Set.univ (arithmeticTupleCanonicalUnitReference (selectedPrimeArithmeticPlaces k K p ι))

open Classical in
def selectedPrimeWeightedHullLogVolume : ℝ :=
  (∑ tuple : ι → FinitePlaceAtPrime k p,
    (1 / (selectedPrimeTupleDegree k K p ι tuple : ℝ)) *
      arithmeticTupleHullUnitLogVolume (selectedPrimeArithmeticPlaces k K p ι) tuple) /
        (fullPrimeArithmeticTensorDimension k p ι : ℝ)

theorem selectedPrimeWeightedHullLogVolume_nonneg :
    0 ≤ selectedPrimeWeightedHullLogVolume k K p ι := by
  classical
  apply div_nonneg _ (Nat.cast_nonneg _)
  exact Finset.sum_nonneg (fun tuple _ => mul_nonneg (by positivity)
    (arithmeticTupleHullUnitLogVolume_nonneg _ _))

section ActualHaar

variable [∀ tuple, MeasurableSpace (SelectedPrimeTupleBlock k K p ι tuple)]
variable [∀ tuple, BorelSpace (SelectedPrimeTupleBlock k K p ι tuple)]

theorem selectedPrimeWeightedHullLogVolume_eq_relativeLogVolume :
    selectedPrimeWeightedHullLogVolume k K p ι =
      selectedPrimeWeightedRelativeLogVolume k K p ι
        (selectedPrimeCanonicalHullGrid k K p ι)
        (selectedPrimeCanonicalUnitReferenceGrid k K p ι) := by
  classical
  have hmass tuple := measure_arithmeticTupleCanonicalRegions_pos_lt_top
    (selectedPrimeArithmeticPlaces k K p ι) tuple Measure.addHaar
  symm
  unfold selectedPrimeCanonicalHullGrid selectedPrimeCanonicalUnitReferenceGrid
  rw [selectedPrimeWeightedRelativeLogVolume_pi _ _ _ _ _ _
    (fun tuple => (hmass tuple).1.1) (fun tuple => (hmass tuple).1.2)
    (fun tuple => (hmass tuple).2.1) (fun tuple => (hmass tuple).2.2)]
  unfold selectedPrimeWeightedHullLogVolume
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro tuple _
  rw [arithmeticTupleCanonicalRegions_relativeLogVolume]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem selectedPrimeWeightedHullLogVolume_mul_prime :
    selectedPrimeWeightedRelativeLogVolume k K p ι
      (Set.pi Set.univ (fun tuple => (p : ℚ_[p]) •
        arithmeticTupleCanonicalHull (selectedPrimeArithmeticPlaces k K p ι) tuple))
      (selectedPrimeCanonicalUnitReferenceGrid k K p ι) =
      -Real.log (p : ℝ) + selectedPrimeWeightedHullLogVolume k K p ι := by
  have hmass tuple := measure_arithmeticTupleCanonicalRegions_pos_lt_top
    (selectedPrimeArithmeticPlaces k K p ι) tuple Measure.addHaar
  have hscale := selectedPrimeWeightedRelativeLogVolume_mul_prime k K p ι
    (arithmeticTupleCanonicalHull (selectedPrimeArithmeticPlaces k K p ι))
    (arithmeticTupleCanonicalUnitReference (selectedPrimeArithmeticPlaces k K p ι))
    (fun tuple => (hmass tuple).1.1) (fun tuple => (hmass tuple).1.2)
    (fun tuple => (hmass tuple).2.1) (fun tuple => (hmass tuple).2.2)
  rw [selectedPrimeWeightedHullLogVolume_eq_relativeLogVolume k K p ι]
  exact hscale

end ActualHaar

variable {J : (ι → FinitePlaceAtPrime k p) → Type (max v w)} [∀ tuple, Finite (J tuple)]
variable {E : (tuple : ι → FinitePlaceAtPrime k p) → J tuple → Type (max v w)}
variable [∀ tuple j, NormedField (E tuple j)] [∀ tuple j, NormedAlgebra ℚ_[p] (E tuple j)]
variable [∀ tuple j, FiniteDimensional ℚ_[p] (E tuple j)] [∀ tuple j, ProperSpace (E tuple j)]

open Classical in
theorem selectedPrimeWeightedHullLogVolume_eq_fieldProducts
    (e : ∀ tuple, SelectedPrimeTupleBlock k K p ι tuple ≃ₐ[ℚ_[p]] ((j : J tuple) → E tuple j)) :
    selectedPrimeWeightedHullLogVolume k K p ι =
      (∑ tuple, (1 / (selectedPrimeTupleDegree k K p ι tuple : ℝ)) *
        (letI : MeasurableSpace ((j : J tuple) → E tuple j) := borel _
         letI : BorelSpace ((j : J tuple) → E tuple j) := ⟨rfl⟩
         normalizedLogVolume Measure.addHaar
           (hull (arithmeticTupleFieldLogImage (selectedPrimeArithmeticPlaces k K p ι) tuple
             (e tuple))))) / (fullPrimeArithmeticTensorDimension k p ι : ℝ) := by
  unfold selectedPrimeWeightedHullLogVolume
  congr 1
  apply Finset.sum_congr rfl
  intro tuple _
  rw [arithmeticTupleHullUnitLogVolume_eq _ _ (e tuple)]

theorem selectedPrimeCanonicalHullGrid_eq_fieldHull_pullback
    (e : ∀ tuple, SelectedPrimeTupleBlock k K p ι tuple ≃ₐ[ℚ_[p]] ((j : J tuple) → E tuple j)) :
    (fun x : (a : Sigma J) → E a.1 a.2 =>
      fun tuple => (e tuple).symm (blockProjection tuple x)) ''
        hull (arithmeticBlockFieldLogImage (selectedPrimeArithmeticPlaces k K p ι) e) =
      selectedPrimeCanonicalHullGrid k K p ι := by
  classical
  have hcompose :
      (fun y : (tuple : ι → FinitePlaceAtPrime k p) → (j : J tuple) → E tuple j =>
        fun tuple => (e tuple).symm (y tuple)) ''
        (blockCoordinatesHomeomorph ''
          hull (arithmeticBlockFieldLogImage (selectedPrimeArithmeticPlaces k K p ι) e)) =
      (fun x : (a : Sigma J) → E a.1 a.2 =>
        fun tuple => (e tuple).symm (blockProjection tuple x)) ''
          hull (arithmeticBlockFieldLogImage (selectedPrimeArithmeticPlaces k K p ι) e) := by
    rw [Set.image_image]
    rfl
  rw [← hcompose, arithmeticBlockFieldHull_eq_pi]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩ tuple _
    rw [arithmeticTupleCanonicalHull_eq _ _ (e tuple)]
    exact ⟨y tuple, hy tuple (Set.mem_univ _), rfl⟩
  · intro hx
    refine ⟨fun tuple => e tuple (x tuple), ?_, ?_⟩
    · intro tuple _
      have htuple := hx tuple (Set.mem_univ _)
      rw [arithmeticTupleCanonicalHull_eq _ _ (e tuple)] at htuple
      rcases htuple with ⟨y, hy, heq⟩
      simpa only [arithmeticTupleFieldLogImage, ← heq, AlgEquiv.apply_symm_apply] using hy
    · funext tuple
      exact (e tuple).symm_apply_apply (x tuple)

theorem selectedPrimeCanonicalUnitReferenceGrid_eq_fieldUnit_pullback
    (e : ∀ tuple, SelectedPrimeTupleBlock k K p ι tuple ≃ₐ[ℚ_[p]] ((j : J tuple) → E tuple j)) :
    (fun x : (a : Sigma J) → E a.1 a.2 =>
      fun tuple => (e tuple).symm (blockProjection tuple x)) ''
        unitRegion (K := fun a : Sigma J => E a.1 a.2) =
      selectedPrimeCanonicalUnitReferenceGrid k K p ι := by
  ext x
  constructor
  · rintro ⟨field, hfield, rfl⟩ tuple _
    rw [arithmeticTupleCanonicalUnitReference_eq _ _ (e tuple)]
    refine ⟨blockProjection tuple field, ?_, rfl⟩
    intro j
    exact hfield ⟨tuple, j⟩
  · intro hx
    refine ⟨fun a => e a.1 (x a.1) a.2, ?_, ?_⟩
    · intro a
      have htuple := hx a.1 (Set.mem_univ _)
      rw [arithmeticTupleCanonicalUnitReference_eq _ _ (e a.1)] at htuple
      rcases htuple with ⟨y, hy, heq⟩
      change ‖e a.1 (x a.1) a.2‖ ≤ 1
      rw [← heq]
      simpa only [AlgEquiv.apply_symm_apply] using hy a.2
    · funext tuple
      change (e tuple).symm (e tuple (x tuple)) = x tuple
      exact (e tuple).symm_apply_apply (x tuple)

open Classical in
theorem selectedPrimeWeightedHullLogVolume_eq_globalFieldFunctional
    (e : ∀ tuple, SelectedPrimeTupleBlock k K p ι tuple ≃ₐ[ℚ_[p]] ((j : J tuple) → E tuple j)) :
    letI : ∀ tuple, MeasurableSpace ((j : J tuple) → E tuple j) := fun _ => borel _
    letI : ∀ tuple, BorelSpace ((j : J tuple) → E tuple j) := fun _ => ⟨rfl⟩
    selectedPrimeWeightedHullLogVolume k K p ι =
      FiniteWeightedProduct.weightedRelativeLogVolume (SelectedPrimeTupleLabels k K p ι)
        (fun tuple => (j : J tuple) → E tuple j) (fun _ => Measure.addHaar)
        (blockCoordinatesHomeomorph ''
          hull (arithmeticBlockFieldLogImage (selectedPrimeArithmeticPlaces k K p ι) e))
        (Set.pi Set.univ (fun tuple => unitRegion (K := E tuple))) /
          (fullPrimeArithmeticTensorDimension k p ι : ℝ) := by
  letI : ∀ tuple, MeasurableSpace ((j : J tuple) → E tuple j) := fun _ => borel _
  letI : ∀ tuple, BorelSpace ((j : J tuple) → E tuple j) := fun _ => ⟨rfl⟩
  have hmass tuple := measure_arithmeticTupleFieldHull_pos_lt_top
    (selectedPrimeArithmeticPlaces k K p ι) tuple (e tuple) Measure.addHaar
  unfold arithmeticTupleFieldLogImage at hmass
  have hunit tuple := measure_unitRegion_pos_lt_top
    (Measure.addHaar : Measure ((j : J tuple) → E tuple j))
  rw [arithmeticBlockFieldHull_eq_pi,
    FiniteWeightedProduct.weightedRelativeLogVolume_pi _ _ _ _ _
      (fun tuple => (hmass tuple).1) (fun tuple => (hmass tuple).2)
      (fun tuple => (hunit tuple).1) (fun tuple => (hunit tuple).2)]
  simpa only [SelectedPrimeTupleLabels, RelativeCompletionTupleLabels, Fintype.card_fin,
    normalizedLogVolume, arithmeticTupleFieldLogImage] using
      selectedPrimeWeightedHullLogVolume_eq_fieldProducts k K p ι e

end

end LeanFormal.IUT.NumberFieldFinitePlace
