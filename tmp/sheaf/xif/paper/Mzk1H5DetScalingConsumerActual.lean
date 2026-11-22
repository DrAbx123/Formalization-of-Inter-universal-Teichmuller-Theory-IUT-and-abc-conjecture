import tmp.sheaf.xif.paper.Mzk1H5DetScalingLawsActualV2
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-! # Mzk1H5DetScalingConsumerActual — H5 determinant scaling-law consumers

DAG node: e-deep:E2.detScalingLaws.  Re-exports the scaling composition, inverse,
power and positivity laws for hull06 log-det.  No new math; no closure.
GATE NOT PASSED; registry 14041; no registry edits. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1H5DetScalingConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Hull06DetTensorActual
open LeanFormal.IUT.XiFPaper.Mzk1H5DetScalingLawsActual

theorem det_scaling_compose_consumer {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.PosDef) {c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    hull06MatrixLogDet ((c * d) • A) =
      (Fintype.card n : ℝ) * Real.log c + (Fintype.card n : ℝ) * Real.log d +
        hull06MatrixLogDet A :=
  hull06_det_scaling_compose hA hc hd

theorem det_scaling_inv_consumer {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.PosDef) {c : ℝ} (hc : 0 < c) :
    hull06MatrixLogDet (c⁻¹ • A) =
      -((Fintype.card n : ℝ) * Real.log c) + hull06MatrixLogDet A :=
  hull06_det_scaling_inv hA hc

theorem det_pow_consumer {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.PosDef) (M : Nat) :
    hull06MatrixLogDet (A ^ M) = (M : ℝ) * hull06MatrixLogDet A :=
  hull06_det_pow hA M

def detScalingConsumerRows : List (String × String × String) :=
  [ ("composition", "det_scaling_compose_consumer", "PROVED (re-export)"),
    ("inverse scaling", "det_scaling_inv_consumer", "PROVED (re-export)"),
    ("power", "det_pow_consumer", "PROVED (re-export)"),
    ("scope", "no new math; no closure; gate NOT PASSED", "INTEGRITY") ]

theorem detScalingConsumerRows_length : detScalingConsumerRows.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1H5DetScalingConsumerActual

end
