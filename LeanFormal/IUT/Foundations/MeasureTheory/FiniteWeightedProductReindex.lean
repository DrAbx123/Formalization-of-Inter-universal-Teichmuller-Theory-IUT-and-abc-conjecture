import LeanFormal.IUT.Foundations.MeasureTheory.FiniteWeightedProductFunctoriality

/-!
# Reindexing the finite coordinate set in III Remark 3.1.1(iv)

A bijection of the coordinate sets induces actual bijections of the full
labels, omitted-coordinate labels, and W. The resulting measurable
reindexing preserves the genuine product measure and the weighted lift.
-/

namespace LeanFormal.IUT.FiniteWeightedProduct

open MeasureTheory

noncomputable section

variable {U V : Type*} (E : V → Type*) (M : V → Type*)
variable [∀ v, MeasurableSpace (M v)] (η : U ≃ V)

def omittedIndexEquiv (u : U) : {t : U // t ≠ u} ≃ {v : V // v ≠ η u} :=
  η.subtypeEquiv (by
    intro t
    constructor
    · intro h heq
      exact h (η.injective heq)
    · intro h heq
      exact h (congrArg η heq))

def productLabelsReindexEquiv : ProductLabels (fun u => E (η u)) ≃ ProductLabels E :=
  Equiv.piCongrLeft E η

def labelsAwayReindexEquiv (u : U) :
    LabelsAway (fun u => E (η u)) u ≃ LabelsAway E (η u) :=
  Equiv.piCongrLeft (fun v : {v : V // v ≠ η u} => E v.val) (omittedIndexEquiv η u)

def weightedIndexReindexEquiv : WeightedIndex (fun u => E (η u)) ≃ WeightedIndex E :=
  Equiv.sigmaCongr η (labelsAwayReindexEquiv E η)

def baseReindexMeasurableEquiv : ((u : U) → M (η u)) ≃ᵐ ((v : V) → M v) :=
  MeasurableEquiv.piCongrLeft M η

def weightedReindexMeasurableEquiv :
    WeightedCoordinates (fun u => E (η u)) (fun u => M (η u)) ≃ᵐ WeightedCoordinates E M :=
  MeasurableEquiv.piCongrLeft (fun w : WeightedIndex E => M w.1)
    (weightedIndexReindexEquiv E η)

theorem restrictLabels_reindex (u : U) (labels : ProductLabels (fun u => E (η u))) :
    labelsAwayReindexEquiv E η u (restrictLabels (fun u => E (η u)) u labels) =
      restrictLabels E (η u) (productLabelsReindexEquiv E η labels) := by
  funext v
  obtain ⟨t, rfl⟩ := (omittedIndexEquiv η u).surjective v
  change (Equiv.piCongrLeft (fun v : {v : V // v ≠ η u} => E v.val)
    (omittedIndexEquiv η u) (restrictLabels (fun u => E (η u)) u labels))
    (omittedIndexEquiv η u t) = (Equiv.piCongrLeft E η labels) (η t.val)
  rw [Equiv.piCongrLeft_apply_apply, Equiv.piCongrLeft_apply_apply]
  rfl

theorem weightedSlice_reindex (labels : ProductLabels (fun u => E (η u)))
    (x : WeightedCoordinates (fun u => E (η u)) (fun u => M (η u))) :
    weightedSlice E M (productLabelsReindexEquiv E η labels)
      (weightedReindexMeasurableEquiv E M η x) =
      baseReindexMeasurableEquiv M η
        (weightedSlice (fun u => E (η u)) (fun u => M (η u)) labels x) := by
  funext v
  obtain ⟨u, rfl⟩ := η.surjective v
  change (weightedReindexMeasurableEquiv E M η x)
    ⟨η u, restrictLabels E (η u) (productLabelsReindexEquiv E η labels)⟩ = _
  rw [← restrictLabels_reindex E η u labels]
  change (Equiv.piCongrLeft (fun w : WeightedIndex E => M w.1)
    (weightedIndexReindexEquiv E η) x)
      (weightedIndexReindexEquiv E η ⟨u, restrictLabels (fun u => E (η u)) u labels⟩) =
    (Equiv.piCongrLeft M η _) (η u)
  rw [Equiv.piCongrLeft_apply_apply, Equiv.piCongrLeft_apply_apply]
  rfl

theorem weightedReindexMeasurableEquiv_preimage_liftRegion
    (S : Set ((u : U) → M (η u))) :
    weightedReindexMeasurableEquiv E M η ⁻¹'
      weightedLiftRegion E M (baseReindexMeasurableEquiv M η '' S) =
      weightedLiftRegion (fun u => E (η u)) (fun u => M (η u)) S := by
  have hmem (y : (u : U) → M (η u)) :
      baseReindexMeasurableEquiv M η y ∈ baseReindexMeasurableEquiv M η '' S ↔ y ∈ S := by
    constructor
    · rintro ⟨z, hz, heq⟩
      exact (baseReindexMeasurableEquiv M η).injective heq ▸ hz
    · intro hy
      exact ⟨y, hy, rfl⟩
  ext x
  constructor
  · intro hx labels
    have hmass := hx (productLabelsReindexEquiv E η labels)
    rw [weightedSlice_reindex E M η, hmem] at hmass
    exact hmass
  · intro hx labels
    obtain ⟨source, rfl⟩ := (productLabelsReindexEquiv E η).surjective labels
    rw [weightedSlice_reindex E M η, hmem]
    exact hx source

variable [Fintype U] [Fintype V] [∀ v, Fintype (E v)]

theorem measurePreserving_weightedReindexMeasurableEquiv
    (μ : (v : V) → Measure (M v)) [∀ v, SigmaFinite (μ v)] :
    MeasurePreserving (weightedReindexMeasurableEquiv E M η)
      (weightedAmbientMeasure (fun u => E (η u)) (fun u => M (η u)) (fun u => μ (η u)))
      (weightedAmbientMeasure E M μ) :=
  measurePreserving_piCongrLeft (fun w : WeightedIndex E => μ w.1)
    (weightedIndexReindexEquiv E η)

theorem weightedMeasureValue_reindex
    (μ : (v : V) → Measure (M v)) [∀ v, SigmaFinite (μ v)]
    (S : Set ((u : U) → M (η u))) :
    weightedMeasureValue (fun u => E (η u)) (fun u => M (η u)) (fun u => μ (η u)) S =
      weightedMeasureValue E M μ (baseReindexMeasurableEquiv M η '' S) := by
  have hpres := measurePreserving_weightedReindexMeasurableEquiv E M η μ
  have hmass := congrArg (fun ν =>
    ν (weightedLiftRegion E M (baseReindexMeasurableEquiv M η '' S))) hpres.map_eq
  rw [MeasurableEquiv.map_apply,
    weightedReindexMeasurableEquiv_preimage_liftRegion E M η] at hmass
  exact hmass

theorem weightedLogVolume_reindex
    (μ : (v : V) → Measure (M v)) [∀ v, SigmaFinite (μ v)]
    (S : Set ((u : U) → M (η u))) :
    weightedLogVolume (fun u => E (η u)) (fun u => M (η u)) (fun u => μ (η u)) S =
      weightedLogVolume E M μ (baseReindexMeasurableEquiv M η '' S) := by
  unfold weightedLogVolume
  rw [weightedMeasureValue_reindex E M η μ S,
    Fintype.card_congr (productLabelsReindexEquiv E η)]

end

end LeanFormal.IUT.FiniteWeightedProduct
