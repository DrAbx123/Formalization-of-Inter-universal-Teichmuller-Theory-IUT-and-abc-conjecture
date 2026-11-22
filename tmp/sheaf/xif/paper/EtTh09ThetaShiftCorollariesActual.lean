import tmp.sheaf.xif.paper.EtTh08ThetaTransformationActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1500000

noncomputable section

/-!
# STEP 0 prior-art: theta shift|oddThetaShift|shift corollaries|transformation package|quotient laws -> hits EtTh08ThetaTransformationActual (ThetaShiftData + etTh08_thetaShift_quotient_eval), OddThetaShift:14 / OddThetaNormalization:29/45 (class-B import-blocked tree theorems) -> REUSE (class A: shift-law corollaries at a = 0, +1, -1, +2 and the normalized quotient at a = +1; no re-proof of the analytic law).

# [EtTh] 09: theta transformation package - shift-law corollaries (class A)

Corpus: papers/motizuki_corpus/text/The Etale Theta Function and its Frobenioid-theoretic
Manifestations.txt, Prop 1.4 (transformation / quasi-periodicity package).
CLASS A (proved here): from the abstract ThetaShiftData of EtTh08, the explicit
shift laws at a = 0, 1, -1, 2 and the normalized quotient f(r*U0)/f(U0).
CLASS B (named, not claimed): the actual analytic odd theta function and its
analytic shift law (tree: OddThetaShift:14 / OddThetaNormalization:29/45; import
blocked by the absent OddThetaTermAlgebra.olean).
Registry frozen 14041.
-/

namespace LeanFormal.IUT.XiFPaper.EtTh09ThetaShiftCorollariesActual

open LeanFormal.IUT.XiFPaper.EtTh08ThetaTransformationActual

universe u

/-- Shift law at a = 0: f(U0) = f(U0) (the sign/scale factors collapse). -/
theorem etTh09_shift_zero {L : Type u} [Field L] {f : L → L} {r U0 : L}
    (h : ThetaShiftData f r U0) :
    f (r ^ (0 : ℤ) * U0) = f U0 := by
  simpa using h.shift 0

/-- Shift law at a = 1: f(r * U0) = -r^(-1) * U0^(-2) * f(U0). -/
theorem etTh09_shift_one {L : Type u} [Field L] {f : L → L} {r U0 : L}
    (h : ThetaShiftData f r U0) :
    f (r * U0) = (-1 : L) * r ^ (-1 : ℤ) * U0 ^ (-2 : ℤ) * f U0 := by
  have hs := h.shift 1
  simpa using hs

/-- Shift law at a = -1: f(r^(-1) * U0) = -r * U0^2 * f(U0). -/
theorem etTh09_shift_neg_one {L : Type u} [Field L] {f : L → L} {r U0 : L}
    (h : ThetaShiftData f r U0) :
    f (r ^ (-1 : ℤ) * U0) = (-1 : L) * r ^ (-1 : ℤ) * U0 ^ (2 : ℤ) * f U0 := by
  have hs := h.shift (-1)
  simpa using hs

/-- Shift law at a = 2: f(r^2 * U0) = r^(-4) * U0^(-4) * f(U0). -/
theorem etTh09_shift_two {L : Type u} [Field L] {f : L → L} {r U0 : L}
    (h : ThetaShiftData f r U0) :
    f (r ^ (2 : ℤ) * U0) = r ^ (-4 : ℤ) * U0 ^ (-4 : ℤ) * f U0 := by
  have hs := h.shift 2
  rw [hs]
  norm_num

/-- Normalized quotient at a = 1: f(r * U0) / f(U0) = -r^(-1) * U0^(-2). -/
theorem etTh09_shift_one_quotient {L : Type u} [Field L] {f : L → L} {r U0 : L}
    (h : ThetaShiftData f r U0) (hf : f U0 ≠ 0) :
    f (r * U0) / f U0 = (-1 : L) * r ^ (-1 : ℤ) * U0 ^ (-2 : ℤ) := by
  rw [etTh09_shift_one h]
  exact mul_div_cancel_right₀ _ hf

/-- The theta transformation package rows. -/
def etTh09Rows : List (String × String × String) :=
  [ ("shift law a = 0 (normalization)", "A", "PROVED etTh09_shift_zero")
  , ("shift law a = 1 and normalized quotient", "A", "PROVED etTh09_shift_one / etTh09_shift_one_quotient")
  , ("shift law a = -1", "A", "PROVED etTh09_shift_neg_one")
  , ("shift law a = 2", "A", "PROVED etTh09_shift_two")
  , ("analytic odd theta function + analytic shift law", "B", "tree-proved OddThetaShift:14 / OddThetaNormalization:29/45; import blocked (OddThetaTermAlgebra.olean absent)")
  , ("theta transformation package / quotient evaluation for i^2=-1", "A", "PROVED EtTh08 etTh08_thetaShift_quotient_eval") ]

/-- The transformation package row record has six rows. -/
theorem etTh09Rows_length : etTh09Rows.length = 6 := rfl

#check etTh09_shift_zero
#check etTh09_shift_one
#check etTh09_shift_neg_one
#check etTh09_shift_two
#check etTh09_shift_one_quotient
#check etTh09Rows_length

end LeanFormal.IUT.XiFPaper.EtTh09ThetaShiftCorollariesActual
end