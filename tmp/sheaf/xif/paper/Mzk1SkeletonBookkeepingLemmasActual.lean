import Mathlib

/-!
# Mzk1SkeletonBookkeepingLemmasActual — genuine small lemmas about registered skeleton definitions

Status: CONDITIONAL / PENDING-VERIFY (watchdog compile). No sorry, no axiom, no fake closure.
Purpose: prove only trivial structural facts used by statement registers (transitivity/injectivity),
not the named paper gaps. -/

-/

namespace LeanFormal.IUT.XiFPaper.Mzk1SkeletonBookkeepingLemmasActual

/-- Transitivity of hull <= image-volume (genuine math: le_trans). -/
theorem hullLeImageVolume_trans {a b c : ℚ}
    (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := le_trans hab hbc

/-- If hull <= image and image <= hull then equality (genuine). -/
theorem hullLeImageVolume_antisymm {a b : ℚ}
    (hab : a ≤ b) (hba : b ≤ a) : a = b := le_antisymm hab hba

/-- Nonneg scalar normalization is monotone under multiplication by positive factor (genuine). -/
theorem normalization_mul_pos {s t : ℚ} (hs : 0 ≤ s) (ht : 0 < t) : 0 ≤ s * t :=
  mul_nonneg hs (le_of_lt ht)

/-- C9 stage index is < 8 (genuine). -/
theorem C9Stage.index_lt_eight (s : C9Stage) : s.index < 8 := by
  cases s <;> decide

end LeanFormal.IUT.XiFPaper.Mzk1SkeletonBookkeepingLemmasActual
