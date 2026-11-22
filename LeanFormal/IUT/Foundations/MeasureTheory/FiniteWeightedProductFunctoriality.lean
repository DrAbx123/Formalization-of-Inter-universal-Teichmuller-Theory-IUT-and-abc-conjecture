import LeanFormal.IUT.Foundations.MeasureTheory.FiniteWeightedProductLogVolume

/-!
# Changing the labels in the actual E-weighted construction

Fiberwise label bijections induce a genuine reindexing of M_W, preserving
its product measure and every lifted region. In particular the set functional
and its logarithmic normalization depend only on the finite cardinalities.
-/

namespace LeanFormal.IUT.FiniteWeightedProduct

open MeasureTheory

noncomputable section

variable {V : Type*} (E F : V → Type*) (M : V → Type*)
variable [∀ v, MeasurableSpace (M v)]

def productLabelsEquiv (e : ∀ v, E v ≃ F v) : ProductLabels E ≃ ProductLabels F :=
  Equiv.piCongrRight e

def labelsAwayEquiv (e : ∀ v, E v ≃ F v) (v : V) : LabelsAway E v ≃ LabelsAway F v :=
  Equiv.piCongrRight (fun w => e w.val)

def weightedIndexLabelsEquiv (e : ∀ v, E v ≃ F v) : WeightedIndex E ≃ WeightedIndex F :=
  Equiv.sigmaCongrRight (labelsAwayEquiv E F e)

def weightedCoordinatesLabelsEquiv (e : ∀ v, E v ≃ F v) :
    WeightedCoordinates E M ≃ᵐ WeightedCoordinates F M :=
  MeasurableEquiv.piCongrLeft (fun w : WeightedIndex F => M w.1)
    (weightedIndexLabelsEquiv E F e)

theorem weightedSlice_labelsEquiv (e : ∀ v, E v ≃ F v)
    (labels : ProductLabels E) (x : WeightedCoordinates E M) :
    weightedSlice F M (productLabelsEquiv E F e labels)
      (weightedCoordinatesLabelsEquiv E F M e x) = weightedSlice E M labels x := by
  funext v
  change (Equiv.piCongrLeft (fun w : WeightedIndex F => M w.1)
    (weightedIndexLabelsEquiv E F e) x)
      (weightedIndexLabelsEquiv E F e ⟨v, restrictLabels E v labels⟩) = _
  exact Equiv.piCongrLeft_apply_apply _ _ _ _

theorem weightedCoordinatesLabelsEquiv_preimage_liftRegion (e : ∀ v, E v ≃ F v)
    (S : Set ((v : V) → M v)) :
    weightedCoordinatesLabelsEquiv E F M e ⁻¹' weightedLiftRegion F M S =
      weightedLiftRegion E M S := by
  ext x
  constructor
  · intro hx labels
    have hmem := hx (productLabelsEquiv E F e labels)
    rwa [weightedSlice_labelsEquiv E F M e] at hmem
  · intro hx labels
    obtain ⟨source, rfl⟩ := (productLabelsEquiv E F e).surjective labels
    rw [weightedSlice_labelsEquiv E F M e]
    exact hx source

variable [Fintype V] [∀ v, Fintype (E v)] [∀ v, Fintype (F v)]

theorem measurePreserving_weightedCoordinatesLabelsEquiv
    (e : ∀ v, E v ≃ F v) (μ : (v : V) → Measure (M v)) [∀ v, SigmaFinite (μ v)] :
    MeasurePreserving (weightedCoordinatesLabelsEquiv E F M e)
      (weightedAmbientMeasure E M μ) (weightedAmbientMeasure F M μ) :=
  measurePreserving_piCongrLeft (fun w : WeightedIndex F => μ w.1)
    (weightedIndexLabelsEquiv E F e)

theorem weightedMeasureValue_labelsEquiv
    (e : ∀ v, E v ≃ F v) (μ : (v : V) → Measure (M v)) [∀ v, SigmaFinite (μ v)]
    (S : Set ((v : V) → M v)) :
    weightedMeasureValue E M μ S = weightedMeasureValue F M μ S := by
  have hpres := measurePreserving_weightedCoordinatesLabelsEquiv E F M e μ
  have hmass := congrArg (fun ν => ν (weightedLiftRegion F M S)) hpres.map_eq
  rw [MeasurableEquiv.map_apply,
    weightedCoordinatesLabelsEquiv_preimage_liftRegion E F M e] at hmass
  exact hmass

theorem weightedLogVolume_labelsEquiv
    (e : ∀ v, E v ≃ F v) (μ : (v : V) → Measure (M v)) [∀ v, SigmaFinite (μ v)]
    (S : Set ((v : V) → M v)) :
    weightedLogVolume E M μ S = weightedLogVolume F M μ S := by
  unfold weightedLogVolume
  rw [weightedMeasureValue_labelsEquiv E F M e μ S,
    Fintype.card_congr (productLabelsEquiv E F e)]

theorem weightedMeasureValue_eq_of_card_eq
    (hcard : ∀ v, Fintype.card (E v) = Fintype.card (F v))
    (μ : (v : V) → Measure (M v)) [∀ v, SigmaFinite (μ v)]
    (S : Set ((v : V) → M v)) :
    weightedMeasureValue E M μ S = weightedMeasureValue F M μ S :=
  weightedMeasureValue_labelsEquiv E F M (fun v => Fintype.equivOfCardEq (hcard v)) μ S

theorem weightedLogVolume_eq_of_card_eq
    (hcard : ∀ v, Fintype.card (E v) = Fintype.card (F v))
    (μ : (v : V) → Measure (M v)) [∀ v, SigmaFinite (μ v)]
    (S : Set ((v : V) → M v)) :
    weightedLogVolume E M μ S = weightedLogVolume F M μ S :=
  weightedLogVolume_labelsEquiv E F M (fun v => Fintype.equivOfCardEq (hcard v)) μ S

section ComponentEquivalences

variable (N : V → Type*) [∀ v, MeasurableSpace (N v)]

def baseComponentsMeasurableEquiv (f : ∀ v, M v ≃ᵐ N v) :
    ((v : V) → M v) ≃ᵐ ((v : V) → N v) :=
  MeasurableEquiv.piCongrRight f

def weightedComponentsMeasurableEquiv (f : ∀ v, M v ≃ᵐ N v) :
    WeightedCoordinates E M ≃ᵐ WeightedCoordinates E N :=
  MeasurableEquiv.piCongrRight (fun w => f w.1)

omit [Fintype V] [∀ v, Fintype (E v)] in
theorem weightedSlice_componentEquiv (f : ∀ v, M v ≃ᵐ N v)
    (labels : ProductLabels E) (x : WeightedCoordinates E M) :
    weightedSlice E N labels (weightedComponentsMeasurableEquiv E M N f x) =
      baseComponentsMeasurableEquiv M N f (weightedSlice E M labels x) := rfl

omit [Fintype V] [∀ v, Fintype (E v)] in
theorem weightedComponentsMeasurableEquiv_preimage_liftRegion (f : ∀ v, M v ≃ᵐ N v)
    (S : Set ((v : V) → M v)) :
    weightedComponentsMeasurableEquiv E M N f ⁻¹'
      weightedLiftRegion E N (baseComponentsMeasurableEquiv M N f '' S) =
      weightedLiftRegion E M S := by
  have hmem (y : (v : V) → M v) :
      baseComponentsMeasurableEquiv M N f y ∈ baseComponentsMeasurableEquiv M N f '' S ↔
        y ∈ S := by
    constructor
    · rintro ⟨z, hz, heq⟩
      exact (baseComponentsMeasurableEquiv M N f).injective heq ▸ hz
    · intro hy
      exact ⟨y, hy, rfl⟩
  ext x
  change (∀ labels, weightedSlice E N labels
    (weightedComponentsMeasurableEquiv E M N f x) ∈ _) ↔ _
  simp only [weightedSlice_componentEquiv, hmem]
  rfl

theorem measurePreserving_weightedComponentsMeasurableEquiv (f : ∀ v, M v ≃ᵐ N v)
    (μ : (v : V) → Measure (M v)) (ν : (v : V) → Measure (N v))
    [∀ v, SigmaFinite (ν v)] (hf : ∀ v, MeasurePreserving (f v) (μ v) (ν v)) :
    MeasurePreserving (weightedComponentsMeasurableEquiv E M N f)
      (weightedAmbientMeasure E M μ) (weightedAmbientMeasure E N ν) :=
  measurePreserving_pi (fun w : WeightedIndex E => μ w.1)
    (fun w : WeightedIndex E => ν w.1) (fun w => hf w.1)

theorem weightedMeasureValue_componentEquiv (f : ∀ v, M v ≃ᵐ N v)
    (μ : (v : V) → Measure (M v)) (ν : (v : V) → Measure (N v))
    [∀ v, SigmaFinite (ν v)] (hf : ∀ v, MeasurePreserving (f v) (μ v) (ν v))
    (S : Set ((v : V) → M v)) :
    weightedMeasureValue E M μ S =
      weightedMeasureValue E N ν (baseComponentsMeasurableEquiv M N f '' S) := by
  have hpres := measurePreserving_weightedComponentsMeasurableEquiv E M N f μ ν hf
  have hmass := congrArg (fun η =>
    η (weightedLiftRegion E N (baseComponentsMeasurableEquiv M N f '' S))) hpres.map_eq
  rw [MeasurableEquiv.map_apply,
    weightedComponentsMeasurableEquiv_preimage_liftRegion E M N f] at hmass
  exact hmass

theorem weightedLogVolume_componentEquiv (f : ∀ v, M v ≃ᵐ N v)
    (μ : (v : V) → Measure (M v)) (ν : (v : V) → Measure (N v))
    [∀ v, SigmaFinite (ν v)] (hf : ∀ v, MeasurePreserving (f v) (μ v) (ν v))
    (S : Set ((v : V) → M v)) :
    weightedLogVolume E M μ S =
      weightedLogVolume E N ν (baseComponentsMeasurableEquiv M N f '' S) := by
  unfold weightedLogVolume
  rw [weightedMeasureValue_componentEquiv E M N f μ ν hf S]

end ComponentEquivalences

end

end LeanFormal.IUT.FiniteWeightedProduct
