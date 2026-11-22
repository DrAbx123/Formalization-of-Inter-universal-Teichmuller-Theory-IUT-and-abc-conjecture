import LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/HullDeterminantLogVolumeReduction

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-!
# Mzk1DetTensorCommutationActual — A479 new determinant-tensor laws

New laws derived from the donor laws of
`HullDeterminantLogVolumeReduction.lean` (:179/197):

1. `matrixLogDet_kronecker_comm_posDef`: the Kronecker log-determinant is
   symmetric in its two positive-definite factors;
2. `matrixLogDet_transpose_posDef`: the log-determinant is invariant under
   transpose of a positive-definite matrix.

Both are new conclusions (not donor aliases): they use the two Kronecker laws /
`Matrix.det_transpose` and commutativity of the card factors.

No sorry/axioms; no closure claim.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1DetTensorCommutationActual

open LeanFormal.IUT

/-- **Kronecker commutation law** for log-determinants of positive-definite
factors. -/
theorem matrixLogDet_kronecker_comm_posDef {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    {A : Matrix m m Real} {B : Matrix n n Real} (hA : A.PosDef) (hB : B.PosDef) :
    matrixLogDet (A ⊗ₖ B) = matrixLogDet (B ⊗ₖ A) := by
  rw [matrixLogDet_kronecker_posDef hA hB,
    matrixLogDet_kronecker_posDef (m := n) (n := m) hB hA]
  ring

/-- **Transpose invariance** of the log-determinant. -/
theorem matrixLogDet_transpose_posDef {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n Real} (hA : A.PosDef) :
    matrixLogDet Aᵀ = matrixLogDet A := by
  unfold matrixLogDet
  rw [Matrix.det_transpose]

#check matrixLogDet_kronecker_comm_posDef
#check matrixLogDet_transpose_posDef

end LeanFormal.IUT.XiFPaper.Mzk1DetTensorCommutationActual
end