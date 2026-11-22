import LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/HullDeterminantLogVolumeReduction

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-!
# Mzk1DetTensorInvolutionLawsActual — A479 new determinant-tensor inverse laws

New laws derived from `HullDeterminantLogVolumeReduction.lean` (:173/233/249/302)
and Mathlib's non-singular inverse determinant (Matrix/Determinant/NonsingularInverse):

1. `matrixLogDet_inv_posDef`: log-det of the inverse = negative log-det;
2. `packetLogVolume_inv_consumer`: the inverse packet diagonal matrix has
   log-det equal to the negative packet log-volume.

No sorry/axioms; no closure claim.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1DetTensorInvolutionLawsActual

open LeanFormal.IUT

/-- **Inverse law**: log-det of the inverse of a positive-definite matrix. -/
theorem matrixLogDet_inv_posDef {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n Real} (hA : A.PosDef) :
    matrixLogDet A⁻¹ = -matrixLogDet A := by
  unfold matrixLogDet
  rw [Matrix.det_nonsing_inv, Real.log_inv]

/-- **Packet inverse consumer**: the inverse packet diagonal matrix has
log-determinant equal to the negative packet log-volume. -/
theorem packetLogVolume_inv_consumer {label : Type*} [Fintype label] [DecidableEq label]
    (p : PositivePacket label) :
    matrixLogDet (packetDiagonalMatrix p)⁻¹ = -packetLogVolume p := by
  rw [matrixLogDet_inv_posDef (packetDiagonalMatrix_posDef p),
    packetLogVolume_eq_matrixLogDet p]

#check matrixLogDet_inv_posDef
#check packetLogVolume_inv_consumer

end LeanFormal.IUT.XiFPaper.Mzk1DetTensorInvolutionLawsActual
end