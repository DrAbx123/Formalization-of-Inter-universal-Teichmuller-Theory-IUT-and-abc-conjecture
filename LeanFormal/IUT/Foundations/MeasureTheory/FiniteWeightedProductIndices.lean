import Mathlib.Logic.Equiv.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-!
# Actual finite indices in III Remark 3.1.1(iv)

The full label set is E=Pi_v E_v; the labels away from v omit its one
coordinate. W is the disjoint union of these omitted-coordinate products.
Every restriction is onto when the omitted coordinate is nonempty.
-/

namespace LeanFormal.IUT.FiniteWeightedProduct

noncomputable section

variable {V : Type*} (E : V → Type*)

abbrev ProductLabels := (v : V) → E v

abbrev LabelsAway (v : V) := (w : {w : V // w ≠ v}) → E w.val

abbrev WeightedIndex := (v : V) × LabelsAway E v

def restrictLabels (v : V) (labels : ProductLabels E) : LabelsAway E v :=
  fun w => labels w.val

def completeLabels [DecidableEq V] (v : V) (label : E v) (away : LabelsAway E v) :
    ProductLabels E :=
  (Equiv.piSplitAt v E).symm (label, away)

theorem restrict_completeLabels [DecidableEq V] (v : V) (label : E v)
    (away : LabelsAway E v) :
    restrictLabels E v (completeLabels E v label away) = away :=
  congrArg Prod.snd ((Equiv.piSplitAt v E).apply_symm_apply (label, away))

theorem restrictLabels_surjective (v : V) [Nonempty (E v)] :
    Function.Surjective (restrictLabels E v) := by
  classical
  intro away
  exact ⟨completeLabels E v (Classical.choice ‹Nonempty (E v)›) away,
    restrict_completeLabels E v _ away⟩

instance productLabelsNonempty [∀ v, Nonempty (E v)] : Nonempty (ProductLabels E) :=
  ⟨fun v => Classical.choice (inferInstance : Nonempty (E v))⟩

instance labelsAwayNonempty [∀ v, Nonempty (E v)] (v : V) : Nonempty (LabelsAway E v) :=
  ⟨fun w => Classical.choice (inferInstance : Nonempty (E w.val))⟩

instance weightedIndexNonempty [Nonempty V] [∀ v, Nonempty (E v)] :
    Nonempty (WeightedIndex E) :=
  ⟨⟨Classical.choice ‹Nonempty V›, Classical.choice (inferInstance : Nonempty (LabelsAway E _))⟩⟩

instance productLabelsFintype [Fintype V] [∀ v, Fintype (E v)] : Fintype (ProductLabels E) := by
  classical
  infer_instance

instance labelsAwayFintype [Fintype V] [∀ v, Fintype (E v)] (v : V) :
    Fintype (LabelsAway E v) := by
  classical
  infer_instance

instance weightedIndexFintype [Fintype V] [∀ v, Fintype (E v)] :
    Fintype (WeightedIndex E) := by
  classical
  infer_instance

theorem card_productLabels_eq_mul_card_labelsAway [Fintype V] [∀ v, Fintype (E v)] (v : V) :
    Fintype.card (ProductLabels E) = Fintype.card (E v) * Fintype.card (LabelsAway E v) := by
  classical
  simpa only [Fintype.card_prod] using Fintype.card_congr (Equiv.piSplitAt v E)

theorem card_productLabels_eq_prod [Fintype V] [∀ v, Fintype (E v)] :
    Fintype.card (ProductLabels E) = ∏ v, Fintype.card (E v) := by
  classical
  exact Fintype.card_pi

theorem card_labelsAway_pos [Fintype V] [∀ v, Fintype (E v)] [∀ v, Nonempty (E v)] (v : V) :
    0 < Fintype.card (LabelsAway E v) := Fintype.card_pos

theorem card_productLabels_pos [Fintype V] [∀ v, Fintype (E v)] [∀ v, Nonempty (E v)] :
    0 < Fintype.card (ProductLabels E) := Fintype.card_pos

end

end LeanFormal.IUT.FiniteWeightedProduct
