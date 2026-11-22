import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic

/-! # Mzk1Stage4NullSetAssemblyActual (stage4 lane; null-set assembly step for B1)

A672 module: the GENERIC assembly step used by B1 in the corrected-region log law —
adding a null set (in particular a singleton image with zero product Haar) does not
change the measure.  This bridges the product law (on the unit-region rectangle) to
the union with the triple-dependent point.  No new mathematics beyond the standard
measure inequalities.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4NullSetAssemblyActual

open MeasureTheory
open scoped ENNReal

universe u
variable {X : Type u} [MeasurableSpace X]

/-- Adding a null set does not change the measure (no measurability needed). -/
theorem measure_union_eq_left_of_null {μ : Measure X} {A B : Set X}
    (hB : μ B = 0) : μ (A ∪ B) = μ A := by
  refine le_antisymm ?_ (measure_mono (Set.subset_union_left))
  calc μ (A ∪ B) ≤ μ A + μ B := measure_union_le _ _
    _ = μ A := by rw [hB, add_zero]

/-- Adding a null set on the right does not change the measure. -/
theorem measure_union_eq_right_of_null {μ : Measure X} {A B : Set X}
    (hA : μ A = 0) : μ (A ∪ B) = μ B := by
  rw [Set.union_comm]
  exact measure_union_eq_left_of_null hA

/-- Image form: if the image of `B` is null, then `f '' (A ∪ B)` has the measure of
`f '' A`. -/
theorem measure_image_union_of_null {μ : Measure X} {f : X → X} {A B : Set X}
    (hB : μ (f '' B) = 0) : μ (f '' (A ∪ B)) = μ (f '' A) := by
  rw [Set.image_union]
  exact measure_union_eq_left_of_null hB

/-- Assembly-step status rows. -/
def nullSetRows : List (String × String) :=
  [ ("union with null set", "measure_union_eq_left_of_null / _right_of_null (PROVED)")
  , ("image union with null image", "measure_image_union_of_null (PROVED)")
  , ("use in B1", "apply with B = {point a b c}: product-Haar singleton nullity (hull lane)")
  , ("next step", "the product law then applies to the scaled unit-region rectangle")
  ]

/-- The null-set record has four rows. -/
theorem nullSetRows_length : nullSetRows.length = 4 := rfl

#check measure_union_eq_left_of_null
#check measure_union_eq_right_of_null
#check measure_image_union_of_null
#check nullSetRows_length

end LeanFormal.IUT.XiFPaper.Mzk1Stage4NullSetAssemblyActual
end
