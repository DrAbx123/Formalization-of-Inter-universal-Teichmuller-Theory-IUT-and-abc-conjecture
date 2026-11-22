import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.HullDeterminantLogVolumeReduction
import tmp.sheaf.xif.paper.Hull06DetTensorActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1H5DetInvLawsConsumerActual — H5 determinant identity/inverse laws (consumer)

DAG node: e-deep:E2.detInvLaws (H5 log-det identity and inverse laws).  The source
statement file Mzk1H5DetInvLawsActual.lean has no fresh olean in the watchdog tree;
this consumer file re-proves the two laws from the tree definitions so the node has
a fresh, self-contained proof path.  No new mathematical content.

No closure claim; GATE NOT PASSED; registry 14041; no registry edits.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1H5DetInvLawsConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Hull06DetTensorActual

/-- Log-determinant of the identity matrix is zero. -/
theorem matrixLogDet_one_consumer (n : Type*) [Fintype n] [DecidableEq n] :
    matrixLogDet (1 : Matrix n n ℝ) = 0 := by
  unfold matrixLogDet
  simp

/-- Log-determinant of the inverse of a positive-definite matrix is the negative. -/
theorem matrixLogDet_inv_posDef_consumer {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.PosDef) :
    matrixLogDet A⁻¹ = -matrixLogDet A := by
  unfold matrixLogDet
  rw [Matrix.det_inv, Real.log_inv]

/-- The hull06 log-det inherits the inverse law from matrixLogDet. -/
theorem hull06MatrixLogDet_inv_posDef {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.PosDef) :
    hull06MatrixLogDet A⁻¹ = -hull06MatrixLogDet A := by
  change matrixLogDet A⁻¹ = -matrixLogDet A
  exact matrixLogDet_inv_posDef_consumer hA

/-- Rows: det inverse-law consumer status. -/
def detInvConsumerRows : List (String × String × String) :=
  [ ("identity law", "matrixLogDet_one_consumer", "PROVED"),
    ("inverse law", "matrixLogDet_inv_posDef_consumer", "PROVED (PosDef)"),
    ("hull06 inverse law", "hull06MatrixLogDet_inv_posDef", "PROVED"),
    ("scope", "no new math; no closure; gate NOT PASSED", "INTEGRITY") ]

theorem detInvConsumerRows_length : detInvConsumerRows.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1H5DetInvLawsConsumerActual

end
