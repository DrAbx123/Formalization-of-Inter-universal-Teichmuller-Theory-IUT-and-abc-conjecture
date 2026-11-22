import LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/HullDeterminantLogVolumeReduction

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-!
# Mzk1DetTensorProductLawsActual — A480 real determinant-tensor laws

New conclusions from the donor laws of
`HullDeterminantLogVolumeReduction.lean` (:179/:197/:213) and Mathlib's
determinant/log-of-product identities:

1. `matrixLogDet_prod_posDef`: log-det of a finite product of
   positive-definite matrices is the sum of the log-dets (new finite-product
   generalization of the two-factor law);
2. `matrixLogDet_laws_package`: the product, power and inverse log-det laws
   hold jointly for positive-definite factors.

No sorry/axioms; no closure claim.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1DetTensorProductLawsActual

open LeanFormal.IUT

/-- **Finite-product law**: log-det of a product of positive-definite matrices
is the sum of the log-dets. -/
theorem matrixLogDet_prod_posDef {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : ι → Matrix n n Real) (hA : ∀ i, (A i).PosDef) :
    matrixLogDet (∏ i, A i) = ∑ i, matrixLogDet (A i) := by
  unfold matrixLogDet
  rw [Matrix.det_prod]
  rw [Real.log_prod]
  intro i _
  exact (hA i).det_pos.ne'

/-- **Joint log-det law package** (product, power, inverse). -/
theorem matrixLogDet_laws_package {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n Real} (hA : A.PosDef) (hB : B.PosDef) (M : Nat) :
    matrixLogDet (A * B) = matrixLogDet A + matrixLogDet B ∧
      matrixLogDet (A ^ M) = (M : Real) * matrixLogDet A ∧
      matrixLogDet A⁻¹ = -matrixLogDet A :=
  ⟨matrixLogDet_mul_posDef hA hB,
   matrixLogDet_pow_posDef hA M,
   matrixLogDet_inv_posDef hA⟩

#check matrixLogDet_prod_posDef
#check matrixLogDet_laws_package

end LeanFormal.IUT.XiFPaper.Mzk1DetTensorProductLawsActual
end