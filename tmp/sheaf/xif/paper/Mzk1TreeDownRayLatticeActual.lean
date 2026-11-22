import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.CardHullRealR9PointMembershipAudit

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-!
# STEP 0 prior-art: R9 down-ray lattice facts -> downRay (R9 audit:56), mem_downRay_iff_le:61 -> PROVED intersection/union/monotonicity facts. No closure.

# Mzk1TreeDownRayLatticeActual — down-ray lattice facts

Registry frozen 14041.  No closure claim.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1TreeDownRayLatticeActual

open LeanFormal.IUT

theorem downRay_inter (a b : ℝ) :
    downRay a ∩ downRay b = downRay (min a b) := by
  ext x
  rw [Set.mem_inter_iff, mem_downRay_iff_le, mem_downRay_iff_le, mem_downRay_iff_le]
  constructor
  · rintro ⟨ha, hb⟩
    exact le_min ha hb
  · intro h
    exact ⟨h.trans (min_le_left _ _), h.trans (min_le_right _ _)⟩

theorem downRay_union (a b : ℝ) :
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

theorem downRay_mono {a b : ℝ} (h : a ≤ b) : downRay a ⊆ downRay b := by
  intro x hx
  rw [mem_downRay_iff_le] at hx ⊢
  linarith

def downRayRows : List (String × String × String) :=
  [ ("intersection = min ray", "PROVED", "downRay_inter")
  , ("union = max ray", "PROVED", "downRay_union")
  , ("threshold monotonicity", "PROVED", "downRay_mono")
  ]

theorem downRayRows_length : downRayRows.length = 3 := rfl

#check downRay_inter
#check downRay_union
#check downRay_mono
#check downRayRows_length

end LeanFormal.IUT.XiFPaper.Mzk1TreeDownRayLatticeActual
end