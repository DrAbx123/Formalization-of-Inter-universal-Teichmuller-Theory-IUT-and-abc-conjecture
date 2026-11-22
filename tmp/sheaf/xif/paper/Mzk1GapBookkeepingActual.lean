/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1N5WeakSkeletonActual
import Mathlib.Tactic

/-! # A1108: gap bookkeeping identities (pure algebra) -/

/-
| field | value |
|---|---|
| Status | PROVED (pure algebra): gap is a BOOKKEEPING identity only |
| 恒等 | `gapOf rhs sF A V = rhs + sF*A - V`; `MOf V gap sF A = V + gap - (sF-1)*A`; `MOf V (gapOf ...) = A + rhs` |
| 含义 | **不引入强版 SSIneq**（不假设 `V >= (sF-1)*A`）；证明义务 = `rhs >= -A` |
| 真证 | `M_eq_A_add_rhs`; `M_nonneg_iff`; `n5Weak_zero_iff_M`; `MOf_eq_N5_MOf` |
| 循环性 | no target assumed; pure ring/linarith |
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1GapBookkeepingActual

open LeanFormal.IUT.XiFPaper.Mzk1N5WeakSkeletonActual

/-- `gap = rhs + sF*A - V` (the paper definition, Gap:521-527). -/
def gapOf (rhs sF A V : Real) : Real := rhs + sF * A - V

/-- `M = V + gap - (sF-1)*A` (our variant value). -/
def MOf (V gap sF A : Real) : Real := V + gap - (sF - 1) * A

/-- **Bookkeeping identity**: substituting `gap` gives `M = A + rhs` (V cancels). -/
theorem M_eq_A_add_rhs (rhs sF A V : Real) :
    MOf V (gapOf rhs sF A V) sF A = A + rhs := by
  unfold MOf gapOf
  ring

/-- **Target equivalence**: `0 <= M <-> -A <= rhs`. -/
theorem M_nonneg_iff (rhs sF A V : Real) :
    0 ≤ MOf V (gapOf rhs sF A V) sF A ↔ -A ≤ rhs := by
  rw [M_eq_A_add_rhs]
  constructor <;> intro h <;> linarith

/-- Same M as the N5 weak skeleton's `MOf`: `A + rhs`. -/
theorem MOf_eq_N5_MOf (A rhs : Real) :
    Mzk1N5WeakSkeletonActual.MOf A rhs = A + rhs := rfl

/-- Merge with `N5Weak 0`: `0 <= M <-> N5Weak A rhs 0`. -/
theorem n5Weak_zero_iff_M (rhs sF A V : Real) :
    (0 ≤ MOf V (gapOf rhs sF A V) sF A) ↔ N5Weak A rhs 0 := by
  rw [M_nonneg_iff, ← N5Weak_zero_iff]

def gapBookkeepingRows : List (String × String) :=
  [ ("gapOf", "rhs + sF*A - V (definition)") ,
    ("MOf", "V + gap - (sF-1)*A (definition)") ,
    ("M_eq_A_add_rhs", "M = A + rhs; V cancels (PROVED, ring)") ,
    ("M_nonneg_iff", "0 <= M <-> -A <= rhs (PROVED)") ,
    ("MOf_eq_N5_MOf", "matches N5 skeleton MOf (rfl)") ,
    ("n5Weak_zero_iff_M", "0 <= M <-> N5Weak A rhs 0 (PROVED)") ,
    ("NOTE", "gap is bookkeeping only; no SSIneq / V >= (sF-1)*A assumed") ]

theorem gapBookkeepingRows_length : gapBookkeepingRows.length = 7 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1GapBookkeepingActual