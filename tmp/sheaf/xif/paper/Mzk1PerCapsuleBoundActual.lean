/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # A1009: per-capsule bound skeleton for `M = (1/nC) * sum_i (A + H_i)` -/

/-
| field | value |
|---|---|
| Status | PARTIAL (skeleton; CapsuleData is the abstract normalization ported from
  `coord/DECOMP-NORMALIZATION.md`; actual `H_i`/`componentVol` port is GAP) |
| 来源 | `nC = l* = (l-1)/2`; `A = absLogQ = logQ/(2l)` (LeftHandSide:81-88, no 1/nC);
  `V/gap/rhs` carry 1/nC from `processionVol` (VcI:741, Gap:895, LogVolume:207);
  unique expansion `M = A + (1/nC) sum_i H_i` |
| 循环性 | `PerCapsuleBound` is the OPEN per-capsule inequality; its statement and proof
  must not depend on `M >= 0`, `SSIneq`, `Corollary312Variant`, or `PaperNormVerdict`.
  This file only proves the arithmetic skeleton (sum/division), no target is assumed. |

This file contains no sorry and no axiom.  The abstract `CapsuleData.H_i` is a placeholder
for the actual per-capsule local term (hullPacket / componentVol / scaled shell); when the
ported definitions are available, `H` is replaced by the actual function and the two
theorems below carry over unchanged. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1PerCapsuleBoundActual

open Finset

/-- Abstract capsule data: capsule count, normalized `A`, per-capsule local term `H_i`. -/
structure CapsuleData where
  nC : Nat
  nC_pos : 0 < nC
  A : Real
  H : Fin nC -> Real

/-- The normalized target `M = A + (1/nC) * sum_i H_i` (`rhs = -R`). -/
noncomputable def MOf (D : CapsuleData) : Real :=
  D.A + (∑ i, D.H i) / (D.nC : Real)

/-- The per-capsule bound: `0 <= A + H_i` for every capsule. -/
def PerCapsuleBound (D : CapsuleData) : Prop :=
  forall i : Fin D.nC, 0 <= D.A + D.H i

/-- `M` is the average of the per-capsule quantities `A + H_i` (A counted once). -/
theorem M_eq_avg (D : CapsuleData) :
    MOf D = (∑ i : Fin D.nC, (D.A + D.H i)) / (D.nC : Real) := by
  unfold MOf
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  have hn : (D.nC : Real) ≠ 0 := by
    exact_mod_cast (Nat.pos_iff_ne_zero.mp D.nC_pos)
  field_simp

/-- **Per-capsule theorem**: `(forall i, 0 <= A + H_i) -> 0 <= M`. -/
theorem M_nonneg_of_perCapsule (D : CapsuleData) (h : PerCapsuleBound D) : 0 <= MOf D := by
  rw [M_eq_avg D]
  apply div_nonneg
  · exact Finset.sum_nonneg fun i _ => h i
  · exact_mod_cast Nat.zero_le D.nC

/-- Expanded statement of the open per-capsule inequality (GAP: actual H_i unknown). -/
def PerCapsuleExpanded (D : CapsuleData) : Prop :=
  forall i : Fin D.nC, 0 <= D.A + D.H i

theorem PerCapsuleExpanded_iff (D : CapsuleData) :
    PerCapsuleExpanded D <-> PerCapsuleBound D :=
  Iff.rfl

def perCapsuleRows : List (String × String) :=
  [ ("MOf", "A + (1/nC) sum_i H_i (rhs = -R)") ,
    ("M_eq_avg", "M = (1/nC) sum_i (A + H_i) (PROVED)") ,
    ("PerCapsuleBound", "forall i, 0 <= A + H_i (OPEN, abstract H)") ,
    ("M_nonneg_of_perCapsule", "PerCapsuleBound -> 0 <= M (PROVED)") ,
    ("actual H_i/componentVol port", "GAP: needs ported hullPacket/componentVol") ]

theorem perCapsuleRows_length : perCapsuleRows.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1PerCapsuleBoundActual
