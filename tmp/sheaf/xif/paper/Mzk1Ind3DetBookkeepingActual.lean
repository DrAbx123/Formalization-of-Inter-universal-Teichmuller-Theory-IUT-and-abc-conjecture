import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.HullDeterminantLogVolumeReduction

/-! # Mzk1Ind3DetBookkeepingActual — determinant-layer bookkeeping for the Ind1/2/3 rung

Real Lean (no sorry/axiom): new log-determinant/packet laws completing the det bookkeeping of
the Ind-hull comparison layer (IUT III Cor 3.12 steps xi-d–xi-g):
* transpose invariance of matrixLogDet,
* double-rescaling composition of packets and its log-volume law (the lambda*O hull form,
  Remark 3.9.5(i), composed twice),
* tensor-power/rescale interaction at the log-volume level.
These are real consequences of the PROVED frozen packet/det laws (no value-model carriers).
Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Ind3DetBookkeepingActual

open LeanFormal.IUT

universe u

/-- Transpose invariance of the matrix log-determinant. -/
theorem matrixLogDet_transpose {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n Real) :
    matrixLogDet (Matrix.transpose A) = matrixLogDet A := by
  unfold matrixLogDet
  rw [Matrix.det_transpose]

/-- Double rescaling of a packet: the two scalar rescalings compose. -/
theorem rescalePacket_mul {label : Type*} [Fintype label]
    (c d : Real) (hc : 0 < c) (hd : 0 < d) (packet : PositivePacket label) :
    rescalePacket c hc (rescalePacket d hd packet) =
      rescalePacket (c * d) (mul_pos hc hd) packet := by
  cases packet with
  | mk scale positive =>
      simp [rescalePacket, mul_assoc]

/-- Log-volume of the double rescaling: the card-weighted sum of both log scalars. -/
theorem packetLogVolume_rescale_mul {label : Type*} [Fintype label]
    (c d : Real) (hc : 0 < c) (hd : 0 < d) (packet : PositivePacket label) :
    packetLogVolume (rescalePacket c hc (rescalePacket d hd packet)) =
      (Fintype.card label : Real) * Real.log c +
        (Fintype.card label : Real) * Real.log d + packetLogVolume packet := by
  rw [packetLogVolume_rescale, packetLogVolume_rescale]
  ring

/-- Rescaling after a tensor power: log-volumes add the card-weighted scalar once. -/
theorem packetLogVolume_rescale_tensor {α β : Type*} [Fintype α] [Fintype β]
    (c : Real) (hc : 0 < c) (p : PositivePacket α) (q : PositivePacket β) :
    packetLogVolume (rescalePacket c hc (tensorPacket p q)) =
      (Fintype.card (α × β) : Real) * Real.log c +
        ((Fintype.card β : Real) * packetLogVolume p +
          (Fintype.card α : Real) * packetLogVolume q) := by
  rw [packetLogVolume_rescale, packetLogVolume_tensor]

theorem matrixLogDet_inv_posDef {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n Real} (hA : A.PosDef) :
    matrixLogDet A⁻¹ = - matrixLogDet A := by
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr (ne_of_gt hA.det_pos)
  have hmul : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hunit
  have hdet : A.det * A⁻¹.det = 1 := by
    have := congrArg Matrix.det hmul
    simpa [Matrix.det_mul, Matrix.det_one] using this
  have h2 : A⁻¹.det = (A.det)⁻¹ := eq_inv_of_mul_eq_one_left hdet
  unfold matrixLogDet
  rw [h2, Real.log_inv]

theorem matrixLogDet_one {n : Type*} [Fintype n] [DecidableEq n] :
    matrixLogDet (1 : Matrix n n Real) = 0 := by
  unfold matrixLogDet
  rw [Matrix.det_one, Real.log_one]

#check matrixLogDet_inv_posDef

#check matrixLogDet_transpose
#check packetLogVolume_rescale_mul

end LeanFormal.IUT.XiFPaper.Mzk1Ind3DetBookkeepingActual
end
