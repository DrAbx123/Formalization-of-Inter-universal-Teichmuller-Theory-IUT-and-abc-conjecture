import tmp.sheaf.xif.paper.Mzk1R9HullConsumerActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # R9/H5 ray lattice (green dep); no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1R9HullRayLatticeActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1R9HullConsumerActual

theorem r9Ray_inter (a b : ℝ) :
    downRay a ∩ downRay b = downRay (min a b) := by
  ext x
  rw [Set.mem_inter_iff, mem_downRay_iff_le, mem_downRay_iff_le, mem_downRay_iff_le]
  exact ⟨fun h => le_min h.1 h.2, fun h => ⟨h.trans (min_le_left _ _), h.trans (min_le_right _ _)⟩⟩

theorem r9Ray_union (a b : ℝ) :
    downRay a ∪ downRay b = downRay (max a b) := by
  ext x
  rw [Set.mem_union, mem_downRay_iff_le, mem_downRay_iff_le, mem_downRay_iff_le]
  constructor
  · rintro (h | h)
    · exact h.trans (le_max_left _ _)
    · exact h.trans (le_max_right _ _)
  · intro h
    rcases le_or_gt x a with hxa | hxa
    · exact Or.inl hxa
    · right
      rcases le_or_gt b a with hba | hba
      · rw [max_eq_left hba] at h
        linarith
      · rw [max_eq_right (le_of_lt hba)] at h
        exact h

theorem r9Ray_mono {a b : ℝ} (h : a ≤ b) : downRay a ⊆ downRay b := by
  intro x hx
  rw [mem_downRay_iff_le] at hx ⊢
  linarith

theorem r9Ray_lattice_bundle :
    (∀ a b : ℝ, downRay a ∩ downRay b = downRay (min a b)) ∧
      (∀ a b : ℝ, downRay a ∪ downRay b = downRay (max a b)) ∧
      (∀ a b : ℝ, a ≤ b → downRay a ⊆ downRay b) :=
  ⟨r9Ray_inter, r9Ray_union, fun _ _ h => r9Ray_mono h⟩

def r9RayLatticeRows : List (String × String × String) :=
  [ ("intersection", "PROVED", "r9Ray_inter"),
    ("union", "PROVED", "r9Ray_union"),
    ("monotonicity", "PROVED", "r9Ray_mono"),
    ("bundle", "PROVED", "r9Ray_lattice_bundle") ]

theorem r9RayLatticeRows_length : r9RayLatticeRows.length = 4 := rfl

#check r9Ray_lattice_bundle
#check r9RayLatticeRows_length

end LeanFormal.IUT.XiFPaper.Mzk1R9HullRayLatticeActual
end