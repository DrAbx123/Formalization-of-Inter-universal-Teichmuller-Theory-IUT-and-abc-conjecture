import LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/HullDeterminantLogVolumeReduction

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-!
# Mzk1DetTensorScaledProductActual — A480 new determinant-tensor law (scaled product)

New conclusion combining Mathlib's determinant-of-scalar-multiple and
determinant-of-product identities with the donor log-det product law
(`HullDeterminantLogVolumeReduction.lean:179`): the log-det of a scalar multiple
of a finite product of positive-definite matrices is the card-weighted log of
the scalar plus the sum of the factor log-dets.

No sorry/axioms; no closure claim.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1DetTensorScaledProductActual

open LeanFormal.IUT

/-- Log-det of a scaled finite product of positive-definite matrices. -/
theorem matrixLogDet_smul_prod_posDef {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : Type*} [Fintype n] [DecidableEq n]
    (c : Real) (hc : 0 < c) (A : ι → Matrix n n Real) (hA : ∀ i, (A i).PosDef) :
    matrixLogDet (c • ∏ i, A i) =
      (Fintype.card n : Real) * Real.log c + ∑ i, matrixLogDet (A i) := by
  unfold matrixLogDet
  rw [Matrix.det_smul]
  rw [Real.log_mul (pow_ne_zero _ hc.ne')
    (Finset.prod_ne_zero_iff.mpr (fun i _ => (hA i).det_pos.ne'))]
  rw [Real.log_pow, Matrix.det_prod, Real.log_prod]
  · ring
  · intro i _
    exact (hA i).det_pos.ne'

#check matrixLogDet_smul_prod_posDef

end LeanFormal.IUT.XiFPaper.Mzk1DetTensorScaledProductActual
end