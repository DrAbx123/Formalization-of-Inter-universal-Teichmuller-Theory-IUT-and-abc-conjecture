import LeanFormal.IUT.Foundations.MeasureTheory.FiniteWeightedProductRegion

/-!
# The actual E-weighted set functional of III Remark 3.1.1(iv)

Put the genuine finite product measure on M_W and push it through the
constructed measurable equivalence to the consistent-grid subspace.
The value on S is the mass of S_E there. This is a set functional on M_V;
it is not declared to be an additive measure on M_V.
-/

namespace LeanFormal.IUT.FiniteWeightedProduct

open MeasureTheory

noncomputable section

variable {V : Type*} [Fintype V] (E : V → Type*) [∀ v, Fintype (E v)]
variable (M : V → Type*) [∀ v, MeasurableSpace (M v)]

def weightedAmbientMeasure (μ : (v : V) → Measure (M v)) : Measure (WeightedCoordinates E M) :=
  Measure.pi (fun w : WeightedIndex E => μ w.1)

def weightedMeasureValue (μ : (v : V) → Measure (M v)) (S : Set ((v : V) → M v)) : ENNReal :=
  weightedAmbientMeasure E M μ (weightedLiftRegion E M S)

variable [∀ v, Nonempty (E v)]

def consistentGridMeasure (μ : (v : V) → Measure (M v)) : Measure (consistentGrid E M) :=
  (weightedAmbientMeasure E M μ).map (consistentGridMeasurableEquiv E M)

theorem consistentGridMeasure_liftRegion (μ : (v : V) → Measure (M v))
    (S : Set ((v : V) → M v)) :
    consistentGridMeasure E M μ (consistentLiftRegion E M S) = weightedMeasureValue E M μ S := by
  unfold consistentGridMeasure
  rw [MeasurableEquiv.map_apply]
  change weightedAmbientMeasure E M μ
    (consistentGridEquiv E M ⁻¹' consistentLiftRegion E M S) = _
  rw [consistentGridEquiv_preimage_liftRegion]
  rfl

theorem weightedMeasureValue_empty (μ : (v : V) → Measure (M v)) :
    weightedMeasureValue E M μ ∅ = 0 := by
  simp only [weightedMeasureValue, weightedLiftRegion_empty, measure_empty]

omit [∀ v, Nonempty (E v)] in
theorem weightedMeasureValue_mono (μ : (v : V) → Measure (M v))
    {S T : Set ((v : V) → M v)} (hST : S ⊆ T) :
    weightedMeasureValue E M μ S ≤ weightedMeasureValue E M μ T := by
  unfold weightedMeasureValue
  exact measure_mono (weightedLiftRegion_mono E M hST)

theorem weightedMeasureValue_pi (μ : (v : V) → Measure (M v)) [∀ v, SigmaFinite (μ v)]
    (S : (v : V) → Set (M v)) :
    weightedMeasureValue E M μ (Set.pi Set.univ S) =
      ∏ v, (μ v (S v)) ^ Fintype.card (LabelsAway E v) := by
  unfold weightedMeasureValue weightedAmbientMeasure
  rw [weightedLiftRegion_pi, Measure.pi_pi, Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro v _
  change (∏ _ : LabelsAway E v, μ v (S v)) = _
  simpa only [Finset.card_univ] using
    (Finset.prod_const (s := (Finset.univ : Finset (LabelsAway E v))) (μ v (S v)))

theorem weightedMeasureValue_pi_pos_lt_top
    (μ : (v : V) → Measure (M v)) [∀ v, SigmaFinite (μ v)]
    (S : (v : V) → Set (M v)) (hpos : ∀ v, 0 < μ v (S v)) (hfin : ∀ v, μ v (S v) < ⊤) :
    0 < weightedMeasureValue E M μ (Set.pi Set.univ S) ∧
      weightedMeasureValue E M μ (Set.pi Set.univ S) < ⊤ := by
  rw [weightedMeasureValue_pi]
  constructor
  · apply bot_lt_iff_ne_bot.mpr
    exact Finset.prod_ne_zero_iff.mpr (fun v _ => pow_ne_zero _ (hpos v).ne')
  · exact ENNReal.prod_lt_top (fun v _ => ENNReal.pow_lt_top (hfin v))

end

end LeanFormal.IUT.FiniteWeightedProduct
