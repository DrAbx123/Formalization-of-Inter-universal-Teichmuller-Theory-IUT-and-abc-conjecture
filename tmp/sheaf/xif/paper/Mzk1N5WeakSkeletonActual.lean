/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # A1044: N5Weak condition skeleton (paper Step (xi-d) lower bound, abstract) -/

/-
| field | value |
|---|---|
| Status | PARTIAL (skeleton; N5Weak is the paper lower bound, NOT derived here) |
| GAP | GAP-N5: `N5Weak C` is the paper Step (xi-d) determinant comparison (`-A - C <= rhs`);
  the geometric content (q-pilot region inside the theta hull) is not formalized. |
| GAP | GAP-DIRECTION: existing S3016/S3017 interfaces give UPPER bounds; they cannot
  produce N5Weak without fixing the sign of `thetaSigned`. |
| GAP | GAP-CPAPER: the paper constant C is abstract; hheight is only needed to PROVE it. |
| 循环性 | The theorems below are pure arithmetic; they do NOT use `M >= 0`, SSIneq,
  Cor312Variant, or `N5Weak 0` as a hypothesis.  No target is assumed. |

This file contains no sorry and no axiom.  It only records the arithmetic skeleton
`N5Weak C -> -C <= M` and its C=0 specialization; the paper-faithful input N5Weak
remains an explicit hypothesis. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1N5WeakSkeletonActual

/-- `N5Weak C`: the theta-hull lower bound up to the explicit error `C`:
`-A - C <= rhs`.  (`A = |log q|`, `rhs = -|log Theta|`.) -/
def N5Weak (A rhs C : Real) : Prop := -A - C <= rhs

/-- `M = A - R = A + rhs` (since `R = -rhs`). -/
def MOf (A rhs : Real) : Real := A + rhs

/-- The paper Thm 1.10 constant (abstract form):
`C = (1 + 20 d_mod/l)(log d_F + log f_F) + 20(e*_mod l + eta_prm)`. -/
def CPaper (l d_mod dF fF eStar eta : Real) : Real :=
  (1 + 20 * d_mod / l) * (Real.log dF + Real.log fF) + 20 * (eStar * l + eta)

/-- `N5Weak` with the paper constant. -/
def N5WeakPaper (A rhs l d_mod dF fF eStar eta : Real) : Prop :=
  N5Weak A rhs (CPaper l d_mod dF fF eStar eta)

/-- **Arithmetic core**: `N5Weak C -> -C <= M`. -/
theorem M_ge_negC_of_N5Weak {A rhs C : Real} (h : N5Weak A rhs C) :
    -C <= MOf A rhs := by
  unfold N5Weak MOf at *
  linarith

/-- **C = 0 specialization**: `N5Weak 0 -> 0 <= M` (conditional Cor 3.12). -/
theorem variant_of_N5Weak_zero {A rhs : Real} (h : N5Weak A rhs 0) :
    0 <= MOf A rhs := by
  have h' := M_ge_negC_of_N5Weak h
  simpa using h'

/-- Error version: `C >= 0` and `N5Weak C` give `M >= -C`. -/
theorem M_ge_negC_of_N5Weak_nonneg {A rhs C : Real} (hC : 0 <= C)
    (h : N5Weak A rhs C) : -C <= MOf A rhs :=
  M_ge_negC_of_N5Weak h

/-- Equivalence form: `N5Weak C <-> -A - C <= rhs`. -/
theorem N5Weak_iff (A rhs C : Real) :
    N5Weak A rhs C <-> -A - C <= rhs := Iff.rfl

/-- `N5Weak 0` is exactly `-A <= rhs` (Cor 3.12 form). -/
theorem N5Weak_zero_iff (A rhs : Real) : N5Weak A rhs 0 <-> -A <= rhs := by
  unfold N5Weak
  constructor <;> intro h <;> linarith

/-- Paper constant unfolds to its definition. -/
theorem CPaper_expand (l d_mod dF fF eStar eta : Real) :
    CPaper l d_mod dF fF eStar eta =
      (1 + 20 * d_mod / l) * (Real.log dF + Real.log fF) + 20 * (eStar * l + eta) :=
  rfl

def n5WeakRows : List (String × String) :=
  [ ("N5Weak", "-A - C <= rhs (paper Step xi-d lower bound, abstract)") ,
    ("MOf", "A - R = A + rhs") ,
    ("CPaper", "paper Thm 1.10 error constant") ,
    ("M_ge_negC_of_N5Weak", "N5Weak C -> -C <= M (PROVED, pure arithmetic)") ,
    ("variant_of_N5Weak_zero", "N5Weak 0 -> 0 <= M (PROVED)") ,
    ("GAP-N5", "geometric Step (xi-d) content NOT formalized") ,
    ("GAP-DIRECTION", "S3016/S3017 upper bounds cannot give N5Weak") ]

theorem n5WeakRows_length : n5WeakRows.length = 7 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1N5WeakSkeletonActual