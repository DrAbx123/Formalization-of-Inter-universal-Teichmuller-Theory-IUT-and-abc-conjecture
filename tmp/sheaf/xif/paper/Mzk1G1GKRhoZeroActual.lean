/- R5: the scale-invariant boundary distance `rhoDist` vanishes exactly on the boundary
points `[0:1]`, `[1:0]`, `[1:1]` of `P1(L)`. REUSE: `Mzk1G1GKRhoDistanceActual.rhoDist`
(this lane). DEDUP: no vanishing criterion existed. -/
import tmp.sheaf.xif.paper.Mzk1G1GKRhoDistanceActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1GKRhoZeroActual
open LeanFormal.IUT.XiFPaper.Mzk1G1GKRhoDistanceActual

variable {L : Type*} [NormedField L]

/-- If the minimum of the nonnegative numbers `|a|`, `|b|`, `|a-b|` is zero, one of them is.
-/
theorem disj_of_min_eq_zero {a b : L}
    (h : min (min ‖a‖ ‖b‖) ‖a - b‖ = 0) : a = 0 ∨ b = 0 ∨ a = b := by
  rcases le_total (min ‖a‖ ‖b‖) ‖a - b‖ with hle | hle
  · rw [min_eq_left hle] at h
    rcases le_total ‖a‖ ‖b‖ with h2 | h2
    · rw [min_eq_left h2] at h
      exact Or.inl (norm_eq_zero.mp h)
    · rw [min_eq_right h2] at h
      exact Or.inr (Or.inl (norm_eq_zero.mp h))
  · rw [min_eq_right hle] at h
    exact Or.inr (Or.inr (sub_eq_zero.mp (norm_eq_zero.mp h)))

/-- `rhoDist` vanishes exactly on the boundary of `P1(L)`. -/
theorem rhoDist_eq_zero_iff (a b : L) :
    rhoDist a b = 0 ↔ a = 0 ∨ b = 0 ∨ a = b := by
  unfold rhoDist
  rw [div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · exact disj_of_min_eq_zero h
    · have h1 : max ‖a‖ ‖b‖ = 0 := h
      have ha : ‖a‖ = 0 := by
        have := le_max_left ‖a‖ ‖b‖
        rw [h1] at this
        exact le_antisymm this (norm_nonneg _)
      exact Or.inl (norm_eq_zero.mp ha)
  · rintro (rfl | rfl | h)
    · left
      rw [norm_zero, zero_sub, norm_neg]
      simp
    · left
      rw [norm_zero, sub_zero]
      simp
    · left
      rw [h, sub_self, norm_zero]
      simp

end LeanFormal.IUT.XiFPaper.Mzk1G1GKRhoZeroActual