import LeanFormal.IUT.Foundations.MeasureTheory.FiniteWeightedProductMeasure
import Mathlib.Tactic.NormNum

/-!
# A concrete nonadditive weighted functional

For two coordinates with label cardinalities 2 and 1 and counting measures
on two-point spaces, two disjoint atoms have weighted mass 1 each, but
their union has weighted mass 4. Thus this actual weighted functional
cannot be an additive measure on the original product.
-/

namespace LeanFormal.IUT.FiniteWeightedProduct

open MeasureTheory

noncomputable section

def unequalBinaryLabels (v : Bool) := Fin (if v then 1 else 2)

instance unequalBinaryLabelsFintype (v : Bool) : Fintype (unequalBinaryLabels v) :=
  inferInstanceAs (Fintype (Fin _))

instance unequalBinaryLabelsNonempty (v : Bool) : Nonempty (unequalBinaryLabels v) := by
  cases v <;> exact ⟨⟨0, by decide⟩⟩

def binaryAtomComponents (bit v : Bool) : Set Bool := if v then {bit} else {false}

def binaryRowComponents (v : Bool) : Set Bool := if v then Set.univ else {false}

def binaryAtomRegion (bit : Bool) : Set (Bool → Bool) :=
  Set.pi Set.univ (binaryAtomComponents bit)

def binaryRowRegion : Set (Bool → Bool) := Set.pi Set.univ binaryRowComponents

theorem card_unequalBinaryLabels_product :
    Fintype.card (ProductLabels unequalBinaryLabels) = 2 := by
  rw [card_productLabels_eq_prod]
  simp [unequalBinaryLabels]

theorem card_unequalBinaryLabels_away_true :
    Fintype.card (LabelsAway unequalBinaryLabels true) = 2 := by
  have hcard := card_productLabels_eq_mul_card_labelsAway unequalBinaryLabels true
  rw [card_unequalBinaryLabels_product] at hcard
  simpa [unequalBinaryLabels] using hcard.symm

theorem weightedMeasureValue_binaryAtom (bit : Bool) :
    weightedMeasureValue unequalBinaryLabels (fun _ => Bool) (fun _ => Measure.count)
      (binaryAtomRegion bit) = 1 := by
  unfold binaryAtomRegion
  rw [weightedMeasureValue_pi]
  simp [binaryAtomComponents]

theorem weightedMeasureValue_binaryRow :
    weightedMeasureValue unequalBinaryLabels (fun _ => Bool) (fun _ => Measure.count)
      binaryRowRegion = 4 := by
  unfold binaryRowRegion
  rw [weightedMeasureValue_pi]
  rw [Fintype.prod_bool]
  change (Measure.count (Set.univ : Set Bool)) ^
    Fintype.card (LabelsAway unequalBinaryLabels true) *
    (Measure.count ({false} : Set Bool)) ^
      Fintype.card (LabelsAway unequalBinaryLabels false) = 4
  have hcount : Measure.count (Set.univ : Set Bool) = 2 := by
    simpa only [Finset.coe_univ, Finset.card_univ, Fintype.card_bool, Nat.cast_ofNat] using
      Measure.count_apply_finset (Finset.univ : Finset Bool)
  rw [card_unequalBinaryLabels_away_true, hcount]
  norm_num

theorem disjoint_binaryAtomRegions : Disjoint (binaryAtomRegion false) (binaryAtomRegion true) := by
  apply Set.disjoint_pi.mpr
  refine ⟨true, Set.mem_univ _, ?_⟩
  simp [binaryAtomComponents]

theorem binaryAtomRegions_union :
    binaryAtomRegion false ∪ binaryAtomRegion true = binaryRowRegion := by
  ext x
  cases h : x true <;>
    simp [binaryAtomRegion, binaryRowRegion, binaryAtomComponents, binaryRowComponents, h]

theorem weightedMeasureValue_not_additiveMeasure :
    ¬ ∃ ν : Measure (Bool → Bool), ∀ S,
      ν S = weightedMeasureValue unequalBinaryLabels (fun _ => Bool)
        (fun _ => Measure.count) S := by
  rintro ⟨ν, hν⟩
  have hadd := measure_union (μ := ν) disjoint_binaryAtomRegions
    (Set.toFinite (binaryAtomRegion true)).measurableSet
  rw [binaryAtomRegions_union, hν, hν, hν, weightedMeasureValue_binaryRow,
    weightedMeasureValue_binaryAtom, weightedMeasureValue_binaryAtom] at hadd
  norm_num at hadd

end

end LeanFormal.IUT.FiniteWeightedProduct
