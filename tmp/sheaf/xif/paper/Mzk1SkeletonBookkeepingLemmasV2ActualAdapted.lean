import Mathlib

/-!
# Mzk1SkeletonBookkeepingLemmasV2ActualAdapted (adapted copy, A475 reuse) — corrected skeleton bookkeeping lemmas

DAG node: foundation:bookkeeping.lemmas (CONDITIONAL; original file has a syntax
error and an undefined C9Stage).  This new file provides the real mathematical
content (order transitivity/antisymmetry and nonnegative normalization) without
the broken C9Stage fragment.  No toy carrier; no sorry/axiom.

No closure claim; GATE NOT PASSED; registry 14041; no registry edits.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1SkeletonBookkeepingLemmasV2ActualAdapted

theorem hullLeImageVolume_trans {a b c : ℚ}
    (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := le_trans hab hbc

theorem hullLeImageVolume_antisymm {a b : ℚ}
    (hab : a ≤ b) (hba : b ≤ a) : a = b := le_antisymm hab hba

theorem normalization_mul_pos {s t : ℚ} (hs : 0 ≤ s) (ht : 0 < t) : 0 ≤ s * t :=
  mul_nonneg hs (le_of_lt ht)

/-- Rows: corrected bookkeeping status. -/
def bookkeepingV2Rows : List (String × String × String) :=
  [ ("transitivity", "hullLeImageVolume_trans", "PROVED"),
    ("antisymmetry", "hullLeImageVolume_antisymm", "PROVED"),
    ("normalization", "normalization_mul_pos", "PROVED"),
    ("dropped", "C9Stage.index_lt_eight (undefined C9Stage)", "REMOVED (broken source)"),
    ("scope", "no closure; gate NOT PASSED", "INTEGRITY") ]

theorem bookkeepingV2Rows_length : bookkeepingV2Rows.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1SkeletonBookkeepingLemmasV2ActualAdapted

end
