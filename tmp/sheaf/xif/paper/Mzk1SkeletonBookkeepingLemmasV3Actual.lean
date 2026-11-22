import Mathlib

/-!
# Mzk1SkeletonBookkeepingLemmasV3Actual — bookkeeping lemmas (V3 route; genuine)

Status: PENDING-VERIFY (watchdog). No sorry, no axiom.
V3 route-around: only safe, genuine lemmas (nine-stage index bound, rational chain lemmas). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1SkeletonBookkeepingLemmasV3Actual

/-- Chain: x ≤ y and y < z implies x < z. -/
theorem hullLeImageVolume_trans {x y z : ℚ} (hxy : x ≤ y) (hyz : y < z) : x < z :=
  lt_of_le_of_lt hxy hyz

/-- Product of nonnegative and positive is nonnegative. -/
theorem normalization_mul_pos {s t : ℚ} (hs : 0 ≤ s) (ht : 0 < t) : 0 ≤ s * t :=
  mul_nonneg hs (le_of_lt ht)

/-- Nine-stage index type. -/
inductive C9Stage : Type
  | p0 | p1 | p2 | p3 | p4 | p5 | p6 | p7 | p8
  deriving DecidableEq, Repr

/-- Stage index. -/
def C9Stage.index : C9Stage → Nat
  | C9Stage.p0 => 0 | C9Stage.p1 => 1 | C9Stage.p2 => 2 | C9Stage.p3 => 3
  | C9Stage.p4 => 4 | C9Stage.p5 => 5 | C9Stage.p6 => 6 | C9Stage.p7 => 7
  | C9Stage.p8 => 8

/-- Genuine lemma: every C9 stage index is < 9. -/
theorem C9Stage.index_lt_nine (s : C9Stage) : s.index < 9 := by
  cases s <;> decide

end LeanFormal.IUT.XiFPaper.Mzk1SkeletonBookkeepingLemmasV3Actual
