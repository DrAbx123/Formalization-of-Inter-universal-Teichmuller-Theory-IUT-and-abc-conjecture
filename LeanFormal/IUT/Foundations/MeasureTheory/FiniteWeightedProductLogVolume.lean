import LeanFormal.IUT.Foundations.MeasureTheory.FiniteWeightedProductMeasure
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Field

/-!
# The E-weighted logarithmic functional of III Remark 3.1.1(iv)

The actual product measure on the consistent-grid model gives the reciprocal
cardinality weights on rectangles. Positive finite component masses are explicit;
no ordinary additive measure on the original product is postulated.
-/

namespace LeanFormal.IUT.FiniteWeightedProduct

open MeasureTheory

noncomputable section

variable {V : Type*} [Fintype V] (E : V → Type*) [∀ v, Fintype (E v)]
variable (M : V → Type*) [∀ v, MeasurableSpace (M v)]

def weightedLogVolume (μ : (v : V) → Measure (M v)) (S : Set ((v : V) → M v)) : ℝ :=
  Real.log (weightedMeasureValue E M μ S).toReal / Fintype.card (ProductLabels E)

def weightedRelativeLogVolume (μ : (v : V) → Measure (M v))
    (S C : Set ((v : V) → M v)) : ℝ :=
  weightedLogVolume E M μ S - weightedLogVolume E M μ C

theorem weightedRelativeLogVolume_self (μ : (v : V) → Measure (M v))
    (S : Set ((v : V) → M v)) : weightedRelativeLogVolume E M μ S S = 0 := sub_self _

variable [∀ v, Nonempty (E v)]

theorem log_weightedMeasureValue_pi
    (μ : (v : V) → Measure (M v)) [∀ v, SigmaFinite (μ v)]
    (S : (v : V) → Set (M v)) (hpos : ∀ v, 0 < μ v (S v)) (hfin : ∀ v, μ v (S v) < ⊤) :
    Real.log (weightedMeasureValue E M μ (Set.pi Set.univ S)).toReal =
      ∑ v, (Fintype.card (LabelsAway E v) : ℝ) * Real.log (μ v (S v)).toReal := by
  rw [weightedMeasureValue_pi, ENNReal.toReal_prod]
  simp only [ENNReal.toReal_pow]
  rw [Real.log_prod (fun v _ => pow_ne_zero _
    (ENNReal.toReal_pos (hpos v).ne' (hfin v).ne).ne')]
  simp only [Real.log_pow]

theorem weightedLogVolume_pi
    (μ : (v : V) → Measure (M v)) [∀ v, SigmaFinite (μ v)]
    (S : (v : V) → Set (M v)) (hpos : ∀ v, 0 < μ v (S v)) (hfin : ∀ v, μ v (S v) < ⊤) :
    weightedLogVolume E M μ (Set.pi Set.univ S) =
      ∑ v, (1 / (Fintype.card (E v) : ℝ)) * Real.log (μ v (S v)).toReal := by
  unfold weightedLogVolume
  rw [log_weightedMeasureValue_pi E M μ S hpos hfin, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro v _
  have hcard : (Fintype.card (ProductLabels E) : ℝ) =
      (Fintype.card (E v) : ℝ) * (Fintype.card (LabelsAway E v) : ℝ) := by
    exact_mod_cast card_productLabels_eq_mul_card_labelsAway E v
  have haway : (Fintype.card (LabelsAway E v) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (card_labelsAway_pos E v).ne'
  rw [hcard]
  field_simp [haway]

theorem weightedRelativeLogVolume_pi
    (μ : (v : V) → Measure (M v)) [∀ v, SigmaFinite (μ v)]
    (S C : (v : V) → Set (M v))
    (hSpos : ∀ v, 0 < μ v (S v)) (hSfin : ∀ v, μ v (S v) < ⊤)
    (hCpos : ∀ v, 0 < μ v (C v)) (hCfin : ∀ v, μ v (C v) < ⊤) :
    weightedRelativeLogVolume E M μ (Set.pi Set.univ S) (Set.pi Set.univ C) =
      ∑ v, (1 / (Fintype.card (E v) : ℝ)) *
        (Real.log (μ v (S v)).toReal - Real.log (μ v (C v)).toReal) := by
  unfold weightedRelativeLogVolume
  rw [weightedLogVolume_pi E M μ S hSpos hSfin,
    weightedLogVolume_pi E M μ C hCpos hCfin, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro v _
  ring

end

end LeanFormal.IUT.FiniteWeightedProduct
