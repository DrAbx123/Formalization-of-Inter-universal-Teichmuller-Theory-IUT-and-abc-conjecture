import LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/HullDeterminantLogVolumeReduction

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-!
# Mzk1ConsumerDetTensorActual — A476 real consumer theorems (determinant tensor)

New conclusions combining existing determinant-tensor donor laws
(`HullDeterminantLogVolumeReduction.lean:179/187/213/233/249/302`):

* `packetLogVolume_mul_consumer`: multiplicativity of packet log-volumes for
  two packets (matrixLogDet_mul_posDef + 2x packetLogVolume_eq_matrixLogDet);
* `packetLogVolume_smul_consumer`: rescaling law of the packet log-volume
  (matrixLogDet_smul_posDef + packetLogVolume_eq_matrixLogDet);
* `packetLogVolume_pow_consumer`: tensor-power law re-derived from
  matrixLogDet_pow_posDef + packetLogVolume_eq_matrixLogDet
  (independent path from packetLogVolume_tensorPower).

No sorry/axioms; no closure claim. Registry frozen 14041.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1ConsumerDetTensorActual

open LeanFormal.IUT

/-- **Packet log-volume multiplicativity consumer.** -/
theorem packetLogVolume_mul_consumer {label : Type*} [Fintype label] [DecidableEq label]
    (p q : PositivePacket label) :
    matrixLogDet (packetDiagonalMatrix p * packetDiagonalMatrix q) =
      packetLogVolume p + packetLogVolume q := by
  rw [matrixLogDet_mul_posDef (packetDiagonalMatrix_posDef p) (packetDiagonalMatrix_posDef q),
    packetLogVolume_eq_matrixLogDet p, packetLogVolume_eq_matrixLogDet q]

/-- **Packet log-volume rescaling consumer.** -/
theorem packetLogVolume_smul_consumer {label : Type*} [Fintype label] [DecidableEq label]
    (c : ℝ) (hc : 0 < c) (p : PositivePacket label) :
    matrixLogDet (c • packetDiagonalMatrix p) =
      (Fintype.card label : ℝ) * Real.log c + packetLogVolume p := by
  rw [matrixLogDet_smul_posDef c hc (packetDiagonalMatrix_posDef p),
    packetLogVolume_eq_matrixLogDet p]

/-- **Packet log-volume power consumer** (second derivation path). -/
theorem packetLogVolume_pow_consumer {label : Type*} [Fintype label] [DecidableEq label]
    (p : PositivePacket label) (M : ℕ) :
    matrixLogDet (packetDiagonalMatrix p ^ M) = (M : ℝ) * packetLogVolume p := by
  rw [matrixLogDet_pow_posDef (packetDiagonalMatrix_posDef p) M,
    packetLogVolume_eq_matrixLogDet p]

#check packetLogVolume_mul_consumer

end LeanFormal.IUT.XiFPaper.Mzk1ConsumerDetTensorActual
end