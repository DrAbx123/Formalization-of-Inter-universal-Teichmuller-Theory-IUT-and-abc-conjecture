import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.CardHullRealR9PointMembershipAudit

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # R9 down-ray set facts (tree-only); no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1TreeR9RaySetActual

open LeanFormal.IUT

theorem downRay_eq_Iic (c : ℝ) : downRay c = Set.Iic c := rfl

theorem downRay_mem_iUnion_iff (x : ℝ) (S : Set ℝ) :
    x ∈ ⋃ c ∈ S, downRay c ↔ ∃ c ∈ S, x ≤ c := by
  constructor
  · intro h
    rcases Set.mem_iUnion.mp h with ⟨c, hc⟩
    rcases Set.mem_iUnion.mp hc with ⟨hS, hx⟩
    exact ⟨c, hS, hx⟩
  · rintro ⟨c, hS, hx⟩
    exact Set.mem_iUnion.mpr ⟨c, Set.mem_iUnion.mpr ⟨hS, hx⟩⟩

theorem downRay_monotone : Monotone downRay := by
  intro a b h x hx
  rw [mem_downRay_iff_le] at hx ⊢
  linarith

def downRaySetRows : List (String × String × String) :=
  [ ("downRay = Iic", "PROVED", "downRay_eq_Iic"),
    ("iUnion membership", "PROVED", "downRay_mem_iUnion_iff"),
    ("monotone", "PROVED", "downRay_monotone") ]

theorem downRaySetRows_length : downRaySetRows.length = 3 := rfl

#check downRay_mem_iUnion_iff
#check downRaySetRows_length

end LeanFormal.IUT.XiFPaper.Mzk1TreeR9RaySetActual
end