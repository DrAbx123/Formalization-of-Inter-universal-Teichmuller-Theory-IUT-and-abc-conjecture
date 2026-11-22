import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.HullDeterminantLogVolumeReduction

/-! # Mzk1DetBookkeeping3Actual — commutation/transport of the determinant bookkeeping

Real Lean (no sorry/axiom): new determinant-layer laws used by the Ind1/2/3 hull comparison:
* the Kronecker (tensor) log-determinant is symmetric in its two positive-definite factors;
* transpose-invariance composed with tensor symmetry;
* packet rescaling commutes with the cardinality weight in the double-rescale law.
All proofs chain the PROVED frozen det laws.  No value-model carriers.  Registry 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1DetBookkeeping3Actual

open LeanFormal.IUT

universe u

/-- Kronecker log-determinant is symmetric in the two positive-definite factors. -/
theorem matrixLogDet_kronecker_comm {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    {A : Matrix m m Real} {B : Matrix n n Real} (hA : A.PosDef) (hB : B.PosDef) :
    matrixLogDet (A ⊗ₖ B) = matrixLogDet (B ⊗ₖ A) := by
  rw [matrixLogDet_kronecker_posDef hA hB, matrixLogDet_kronecker_posDef hB hA]
  ring

/-- Transpose-invariance transported through the Kronecker law. -/
theorem matrixLogDet_kronecker_transpose {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    {A : Matrix m m Real} {B : Matrix n n Real} (hA : A.PosDef) (hB : B.PosDef) :
    matrixLogDet ((Matrix.transpose A) ⊗ₖ (Matrix.transpose B)) =
      matrixLogDet (A ⊗ₖ B) := by
  change matrixLogDet (Matrix.kroneckerMap (fun a b : Real => a * b)
    (Matrix.transpose A) (Matrix.transpose B)) =
    matrixLogDet (Matrix.kroneckerMap (fun a b : Real => a * b) A B)
  rw [Matrix.kroneckerMap_transpose]
  rw [matrixLogDet_transpose]

/-- The double-rescale log-volume law is symmetric in the two scalars. -/
theorem packetLogVolume_rescale_mul_comm {label : Type*} [Fintype label]
    (c d : Real) (hc : 0 < c) (hd : 0 < d) (packet : PositivePacket label) :
    packetLogVolume (rescalePacket c hc (rescalePacket d hd packet)) =
      packetLogVolume (rescalePacket d hd (rescalePacket c hc packet)) := by
  rw [packetLogVolume_rescale, packetLogVolume_rescale]
  ring

/-- Log-determinant of a positive diagonal matrix is the sum of logarithms. -/
theorem matrixLogDet_diagonal_pos {n : Type*} [Fintype n] [DecidableEq n]
    (d : n → Real) (h : ∀ i, 0 < d i) :
    matrixLogDet (Matrix.diagonal d) = ∑ i, Real.log (d i) := by
  unfold matrixLogDet
  rw [Matrix.det_diagonal, Real.log_prod (fun i _ => ne_of_gt (h i))]

/-- Packet log-volume is the log-determinant of the packet diagonal matrix. -/
theorem packetLogVolume_eq_matrixLogDet_diagonal {label : Type*} [Fintype label]
    [DecidableEq label] (packet : PositivePacket label) :
    packetLogVolume packet = matrixLogDet (packetDiagonalMatrix packet) := by
  rw [packetLogVolume_eq_log_det, packetDet_eq_packetDiagonalMatrix_det]
  rfl

theorem matrixLogDet_smul_pow {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n Real} (hA : A.PosDef) (c : Real) (hc : 0 < c) (M : Nat) :
    matrixLogDet ((c • A) ^ M) =
      (M : Real) * ((Fintype.card n : Real) * Real.log c + matrixLogDet A) := by
  unfold matrixLogDet
  rw [Matrix.det_pow, Matrix.det_smul, Real.log_pow]
  have hcne : c ≠ 0 := ne_of_gt hc
  have hAne : A.det ≠ 0 := ne_of_gt hA.det_pos
  rw [Real.log_mul (pow_ne_zero _ hcne) hAne, Real.log_pow]
  ring

#check matrixLogDet_smul_pow

#check matrixLogDet_diagonal_pos

#check matrixLogDet_kronecker_comm
#check packetLogVolume_rescale_mul_comm

end LeanFormal.IUT.XiFPaper.Mzk1DetBookkeeping3Actual
end
