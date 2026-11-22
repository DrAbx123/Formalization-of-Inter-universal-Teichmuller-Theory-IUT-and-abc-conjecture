import LeanFormal.IUT.Foundations.MeasureTheory.FiniteWeightedProductIndices
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# The actual consistent grids and lifted regions of III Remark 3.1.1(iv)

Coordinates are indexed by W=Sigma_v E_neq_v. Reading them along a full
label gives a slice in M_V. The resulting grids are exactly those constant
on the fibers of each restriction E -> E_neq_v. This is an actual
homeomorphism, and the weighted lift of a measurable region is measurable.
-/

namespace LeanFormal.IUT.FiniteWeightedProduct

noncomputable section

variable {V : Type*} (E : V → Type*) (M : V → Type*)

abbrev WeightedCoordinates := (w : WeightedIndex E) → M w.1

abbrev GridCoordinates := ProductLabels E → (v : V) → M v

def weightedSlice (labels : ProductLabels E) (x : WeightedCoordinates E M) : (v : V) → M v :=
  fun v => x ⟨v, restrictLabels E v labels⟩

def consistentGrid : Set (GridCoordinates E M) :=
  {grid | ∀ v first second, restrictLabels E v first = restrictLabels E v second →
    grid first v = grid second v}

def coordinatesToGrid (x : WeightedCoordinates E M) : GridCoordinates E M :=
  fun labels => weightedSlice E M labels x

theorem coordinatesToGrid_consistent (x : WeightedCoordinates E M) :
    coordinatesToGrid E M x ∈ consistentGrid E M := by
  intro v first second heq
  change x ⟨v, restrictLabels E v first⟩ = x ⟨v, restrictLabels E v second⟩
  rw [heq]

def weightedLiftRegion (S : Set ((v : V) → M v)) : Set (WeightedCoordinates E M) :=
  {x | ∀ labels, weightedSlice E M labels x ∈ S}

def consistentLiftRegion (S : Set ((v : V) → M v)) : Set (consistentGrid E M) :=
  {grid | ∀ labels, grid.val labels ∈ S}

theorem weightedLiftRegion_eq_iInter (S : Set ((v : V) → M v)) :
    weightedLiftRegion E M S = ⋂ labels, weightedSlice E M labels ⁻¹' S := by
  ext x
  simp only [Set.mem_iInter, Set.mem_preimage]
  rfl

theorem consistentLiftRegion_eq_iInter (S : Set ((v : V) → M v)) :
    consistentLiftRegion E M S =
      ⋂ labels, {grid : consistentGrid E M | grid.val labels ∈ S} := by
  ext grid
  simp only [Set.mem_iInter, Set.mem_setOf_eq]
  rfl

variable [∀ v, Nonempty (E v)]

def consistentGridEquiv : WeightedCoordinates E M ≃ consistentGrid E M := by
  classical
  exact {
    toFun := fun x => ⟨coordinatesToGrid E M x, coordinatesToGrid_consistent E M x⟩
    invFun := fun grid w => grid.val
      (completeLabels E w.1 (Classical.choice (inferInstance : Nonempty (E w.1))) w.2) w.1
    left_inv := by
      intro x
      funext w
      change x ⟨w.1, restrictLabels E w.1
        (completeLabels E w.1 (Classical.choice (inferInstance : Nonempty (E w.1))) w.2)⟩ = x w
      rw [restrict_completeLabels]
    right_inv := by
      intro grid
      apply Subtype.ext
      funext labels v
      exact grid.property v _ labels (restrict_completeLabels E v _ _)
  }

theorem consistentGridEquiv_preimage_liftRegion (S : Set ((v : V) → M v)) :
    consistentGridEquiv E M ⁻¹' consistentLiftRegion E M S = weightedLiftRegion E M S := rfl

theorem weightedLiftRegion_pi (S : (v : V) → Set (M v)) :
    weightedLiftRegion E M (Set.pi Set.univ S) =
      Set.pi Set.univ (fun w : WeightedIndex E => S w.1) := by
  ext x
  constructor
  · intro hx w _
    rcases w with ⟨v, away⟩
    obtain ⟨labels, hlabels⟩ := restrictLabels_surjective E v away
    have hmem := hx labels v (Set.mem_univ v)
    change x ⟨v, restrictLabels E v labels⟩ ∈ S v at hmem
    rw [hlabels] at hmem
    exact hmem
  · intro hx labels v _
    exact hx ⟨v, restrictLabels E v labels⟩ (Set.mem_univ _)

theorem weightedLiftRegion_empty : weightedLiftRegion E M ∅ = ∅ := by
  ext x
  constructor
  · intro hx
    exact hx (Classical.choice (inferInstance : Nonempty (ProductLabels E)))
  · exact False.elim

omit [∀ v, Nonempty (E v)] in
theorem weightedLiftRegion_mono {S T : Set ((v : V) → M v)} (hST : S ⊆ T) :
    weightedLiftRegion E M S ⊆ weightedLiftRegion E M T :=
  fun _ hx labels => hST (hx labels)

section Topology

variable [∀ v, TopologicalSpace (M v)]

omit [∀ v, Nonempty (E v)] in
theorem continuous_weightedSlice (labels : ProductLabels E) :
    Continuous (weightedSlice E M labels) :=
  continuous_pi (fun v => continuous_apply (⟨v, restrictLabels E v labels⟩ : WeightedIndex E))

def consistentGridHomeomorph : WeightedCoordinates E M ≃ₜ consistentGrid E M := by
  classical
  exact {
    toEquiv := consistentGridEquiv E M
    continuous_toFun :=
      (continuous_pi (fun labels => continuous_weightedSlice E M labels)).subtype_mk _
    continuous_invFun := continuous_pi (fun w => (continuous_apply w.1).comp
      ((continuous_apply
        (completeLabels E w.1 (Classical.choice (inferInstance : Nonempty (E w.1))) w.2)).comp
        continuous_subtype_val))
  }

end Topology

section Measurability

variable [∀ v, MeasurableSpace (M v)]

omit [∀ v, Nonempty (E v)] in
theorem measurable_weightedSlice (labels : ProductLabels E) :
    Measurable (weightedSlice E M labels) :=
  measurable_pi_lambda _
    (fun v => measurable_pi_apply (⟨v, restrictLabels E v labels⟩ : WeightedIndex E))

def consistentGridMeasurableEquiv : WeightedCoordinates E M ≃ᵐ consistentGrid E M := by
  classical
  exact {
    toEquiv := consistentGridEquiv E M
    measurable_toFun :=
      (measurable_pi_lambda _ (fun labels => measurable_weightedSlice E M labels)).subtype_mk
    measurable_invFun := measurable_pi_lambda _ (fun w => (measurable_pi_apply w.1).comp
      ((measurable_pi_apply
        (completeLabels E w.1 (Classical.choice (inferInstance : Nonempty (E w.1))) w.2)).comp
        measurable_subtype_coe))
  }

omit [∀ v, Nonempty (E v)] in
theorem measurableSet_weightedLiftRegion [Finite V] [∀ v, Finite (E v)]
    {S : Set ((v : V) → M v)} (hS : MeasurableSet S) :
    MeasurableSet (weightedLiftRegion E M S) := by
  classical
  letI := Fintype.ofFinite V
  letI : ∀ v, Fintype (E v) := fun v => Fintype.ofFinite (E v)
  rw [weightedLiftRegion_eq_iInter]
  exact MeasurableSet.iInter (fun labels => hS.preimage (measurable_weightedSlice E M labels))

omit [∀ v, Nonempty (E v)] in
theorem measurableSet_consistentLiftRegion [Finite V] [∀ v, Finite (E v)]
    {S : Set ((v : V) → M v)} (hS : MeasurableSet S) :
    MeasurableSet (consistentLiftRegion E M S) := by
  classical
  letI := Fintype.ofFinite V
  letI : ∀ v, Fintype (E v) := fun v => Fintype.ofFinite (E v)
  rw [consistentLiftRegion_eq_iInter]
  exact MeasurableSet.iInter (fun labels =>
    hS.preimage ((measurable_pi_apply labels).comp measurable_subtype_coe))

end Measurability

end

end LeanFormal.IUT.FiniteWeightedProduct
