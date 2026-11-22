/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1GapBookkeepingActual
import Mathlib.Tactic

/-! # A1109: hull enlargement term E and the enlarged inequality (pure algebra) -/

/-
| field | value |
|---|---|
| Status | PROVED (pure algebra); E = hull enlargement (Ind1/Ind2/Ind3) |
| 定义在前 | `rhsOf D = V + E - sF*A`; `MOf D = V + E - (sF-1)*A` |
| 不等式在后 | `target_of_enlargement`; `target_of_growth` |
| 真证 | `M_eq_A_add_rhs`; `target_of_enlargement`; `target_of_growth`; `E_eq_gapOf` |
| 循环性 | no target assumed; E is explicit data, not an assumption of the variant form |
| 说明 | faithful 实例化（E = Ind1/Ind2/Ind3 hull enlargement）是下一步；本文件只做代数 |
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1EnlargementActual

open LeanFormal.IUT.XiFPaper.Mzk1GapBookkeepingActual

/-- Hull enlargement data: `A = |log q|`, `V = logVol(hull vcI)`, `E = hull enlargement term`,
`sF = sFactor nC`.  `rhs := V + E - sF*A`. -/
structure EnlargementData where
  A : Real
  V : Real
  E : Real
  sF : Real

/-- `rhs = V + E - sF*A` (the enlargement moves the hull upper bound by `E`). -/
def rhsOf (D : EnlargementData) : Real := D.V + D.E - D.sF * D.A

/-- `M = V + E - (sF-1)*A` (our variant value with the enlargement term). -/
def MOf (D : EnlargementData) : Real := D.V + D.E - (D.sF - 1) * D.A

/-- **Bookkeeping identity**: `M = A + rhs`. -/
theorem M_eq_A_add_rhs (D : EnlargementData) : MOf D = D.A + rhsOf D := by
  unfold MOf rhsOf
  ring

/-- **Enlargement criterion**: if the enlargement covers the deficit `(sF-1)*A - V`,
then the variant holds. -/
theorem target_of_enlargement (D : EnlargementData)
    (h : (D.sF - 1) * D.A - D.V ≤ D.E) : 0 ≤ MOf D := by
  unfold MOf
  linarith

/-- **Growth form**: if `E = c*A`, the criterion becomes `(sF-1-c)*A <= V`. -/
theorem target_of_growth (D : EnlargementData) (c : Real) (hE : D.E = c * D.A)
    (h : (D.sF - 1 - c) * D.A ≤ D.V) : 0 ≤ MOf D := by
  unfold MOf
  rw [hE]
  have h' : D.V + c * D.A - (D.sF - 1) * D.A =
      D.V - (D.sF - 1 - c) * D.A := by ring
  rw [h']
  linarith

/-- **Bridge to gap bookkeeping**: `rhsOf D = rhs ↔ E = gapOf rhs sF A V`. -/
theorem E_eq_gapOf (D : EnlargementData) (rhs : Real) :
    rhsOf D = rhs ↔ D.E = gapOf rhs D.sF D.A D.V := by
  unfold rhsOf gapOf
  constructor <;> intro h <;> linarith

def enlargementRows : List (String × String) :=
  [ ("EnlargementData", "A/V/E/sF") ,
    ("rhsOf", "V + E - sF*A") ,
    ("MOf", "V + E - (sF-1)*A") ,
    ("M_eq_A_add_rhs", "M = A + rhs (PROVED, ring)") ,
    ("target_of_enlargement", "(sF-1)A - V <= E -> 0 <= M (PROVED)") ,
    ("target_of_growth", "E = c*A and (sF-1-c)A <= V -> 0 <= M (PROVED)") ,
    ("E_eq_gapOf", "rhsOf = rhs <-> E = gapOf rhs sF A V (PROVED)") ,
    ("NEXT", "instantiate E = Ind1/Ind2/Ind3 hull enlargement (faithful)") ]

theorem enlargementRows_length : enlargementRows.length = 8 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1EnlargementActual