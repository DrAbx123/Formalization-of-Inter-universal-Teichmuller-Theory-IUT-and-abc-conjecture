/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # P7: formal shell-defect / tame cancellation inventory

lana green statements (read from `Iut/WallEquiv/VcI.lean`; not importable in
the vendor build yet, olean absent):
* `shellExcess_eq_tame` (:414): shell excess = `∑_j (1 − 1/ramIdx_j) log p`;
* `componentVol_leastHull_tensorLogShell_eq_tame` (:435):
  `μ^log(hull(⊗I)) = ∑_j (1 − 1/e_j) log p`;
* `shellDefect_eq_neg_orderVol_tame` (:450): `shellDefect = −orderVol`;
* `hullPacket_tame` (:844), `defectPacket_tame_le` (:870):
  `defectPacket = −∑_c w_c·orderVol_c` and `defectPacket ≤ ∑_c w_c d_c log p`.

Here we formalize the *arithmetic content* of the cancellation (the lana
analytic identities are cited, not re-proved): if the shell defect is the
negative of the packet index term, the weighted defect packet cancels the
index term exactly; the tame bound is then immediate. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1P7TameCancellationActual

open scoped BigOperators

/-- The tame shell defect and order volume in the lana normalization:
`shellDefect = -orderVol`. -/
def tameCancellation (shellDefect orderVol : ℝ) : Prop := shellDefect = -orderVol

theorem tameCancellation_iff (shellDefect orderVol : ℝ) :
    tameCancellation shellDefect orderVol ↔ shellDefect + orderVol = 0 := by
  unfold tameCancellation
  constructor <;> intro h <;> linarith

/-- Weighted defect packet `∑_c w_c·shellDefect_c`. -/
def defectPacket {ι : Type*} [Fintype ι] (w ord : ι → ℝ) : ℝ :=
  ∑ i, w i * (-ord i)

/-- Weighted order/index packet `∑_c w_c·orderVol_c`. -/
def orderVolPacket {ι : Type*} [Fintype ι] (w ord : ι → ℝ) : ℝ :=
  ∑ i, w i * ord i

/-- **Tame cancellation**: `defectPacket = -orderVolPacket`. -/
theorem defectPacket_eq_neg_orderVolPacket {ι : Type*} [Fintype ι]
    (w ord : ι → ℝ) :
    defectPacket w ord = -orderVolPacket w ord := by
  unfold defectPacket orderVolPacket
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- **Tame bound**: if `orderVol_c >= 0` then the defect packet is nonpositive. -/
theorem defectPacket_nonpos_of_orderVol_nonneg {ι : Type*} [Fintype ι]
    (w ord : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hord : ∀ i, 0 ≤ ord i) :
    defectPacket w ord ≤ 0 := by
  rw [defectPacket_eq_neg_orderVolPacket]
  have h : 0 ≤ orderVolPacket w ord := by
    unfold orderVolPacket
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (hord i)
  linarith

/-- `hullPacket_tame` shape: `hullPacket = orderVolPacket + defectPacket`; by the
tame cancellation, it equals `orderVolPacket − orderVolPacket = 0` when the
defect is the negative index term.  This is the algebraic content of lana's
tame hull identity. -/
def hullPacket (orderVolPacket defectPacket : ℝ) : ℝ := orderVolPacket + defectPacket

theorem hullPacket_tame_eq_zero (w ord : ι → ℝ) [Fintype ι]
    (h : defectPacket w ord = -orderVolPacket w ord) :
    hullPacket (orderVolPacket w ord) (defectPacket w ord) = 0 := by
  unfold hullPacket
  rw [h]
  ring

/-- Tame sharp volume formula `∑_j (1 − 1/e_j)·log p` (lana :435). -/
def tameLeastHullVol {ι : Type*} [Fintype ι] (e : ι → ℝ) (logp : ℝ) : ℝ :=
  ∑ i, (1 - 1 / e i) * logp

theorem tameLeastHullVol_sum (e : ι → ℝ) [Fintype ι] (logp : ℝ) :
    tameLeastHullVol e logp = (∑ i, (1 - 1 / e i)) * logp := by
  unfold tameLeastHullVol
  rw [Finset.sum_mul]

def tameRows : List (String × String × String) :=
  [ ("tame shell excess", "shellExcess = sum_j (1-1/e_j) log p", "LANA GREEN (VcI.lean:414 shellExcess_eq_tame)"),
    ("tame hull volume", "mu^log(hull(tensor I)) = sum_j (1-1/e_j) log p", "LANA GREEN (VcI.lean:435 componentVol_leastHull_tensorLogShell_eq_tame)"),
    ("tame shell defect", "shellDefect = -orderVol", "LANA GREEN (VcI.lean:450 shellDefect_eq_neg_orderVol_tame)"),
    ("tame defect packet", "defectPacket = -sum_c w_c orderVol_c", "PROVED arithmetic (defectPacket_eq_neg_orderVolPacket) + LANA GREEN :870"),
    ("tame defect bound", "defectPacket <= sum_c w_c d_c log p", "LANA GREEN (VcI.lean:870 defectPacket_tame_le)"),
    ("cancellation", "defectPacket = -orderVolPacket => hullPacket = 0", "PROVED (hullPacket_tame_eq_zero)"),
    ("tame hull formula", "sum_j (1-1/e_j) log p", "PROVED shape (tameLeastHullVol_sum)"),
    ("gap", "the lana analytic shell-defect identity is cited, not re-proved; VcI.olean absent in vendor build", "EXTERNAL/LANA GREEN") ]

theorem tameRows_length : tameRows.length = 8 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1P7TameCancellationActual.defectPacket_eq_neg_orderVolPacket
#print axioms LeanFormal.IUT.XiFPaper.Mzk1P7TameCancellationActual.defectPacket_nonpos_of_orderVol_nonneg
#print axioms LeanFormal.IUT.XiFPaper.Mzk1P7TameCancellationActual.hullPacket_tame_eq_zero

end LeanFormal.IUT.XiFPaper.Mzk1P7TameCancellationActual

end