import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.HullDeterminantLogVolumeReduction

/-! # Mzk1PacketVolumeConsumerGlueActual — consumer log-volume laws for positive packets

Small glue module (no new mathematics): composes the proved packet identities
(`packetLogVolume_eq_matrixLogDet`, `packetDiagonalMatrix_rescale`/`_tensor`,
`matrixLogDet_smul_posDef`, `matrixLogDet_kronecker_posDef`) into log-volume laws.
Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1PacketVolumeConsumerGlueActual

open LeanFormal.IUT

universe u

/-- Log-volume of a rescaled packet: one cardinal-times-log scalar term. -/
theorem packetLogVolume_rescale_eq {label : Type*} [Fintype label] [DecidableEq label]
    (c : Real) (hc : 0 < c) (packet : PositivePacket label) :
    packetLogVolume (rescalePacket c hc packet) =
      (Fintype.card label : Real) * Real.log c + packetLogVolume packet := by
  rw [packetLogVolume_eq_matrixLogDet, packetDiagonalMatrix_rescale c hc packet,
    matrixLogDet_smul_posDef c hc (packetDiagonalMatrix_posDef packet),
    ← packetLogVolume_eq_matrixLogDet]

/-- Log-volume of a tensor packet: the two component volumes with swapped cardinals. -/
theorem packetLogVolume_tensor_eq {alpha beta : Type*} [Fintype alpha] [Fintype beta]
    [DecidableEq alpha] [DecidableEq beta]
    (p : PositivePacket alpha) (q : PositivePacket beta) :
    packetLogVolume (tensorPacket p q) =
      (Fintype.card beta : Real) * packetLogVolume p +
        (Fintype.card alpha : Real) * packetLogVolume q := by
  rw [packetLogVolume_eq_matrixLogDet, packetDiagonalMatrix_tensor p q,
    matrixLogDet_kronecker_posDef (packetDiagonalMatrix_posDef p)
      (packetDiagonalMatrix_posDef q),
    ← packetLogVolume_eq_matrixLogDet, ← packetLogVolume_eq_matrixLogDet]

/-- Rescaling a tensor packet: scalar term plus the two component volumes. -/
theorem packetLogVolume_rescale_tensor_eq {alpha beta : Type*} [Fintype alpha]
    [Fintype beta] [DecidableEq alpha] [DecidableEq beta]
    (c : Real) (hc : 0 < c) (p : PositivePacket alpha) (q : PositivePacket beta) :
    packetLogVolume (rescalePacket c hc (tensorPacket p q)) =
      ((Fintype.card alpha : Real) * (Fintype.card beta : Real)) * Real.log c +
        (Fintype.card beta : Real) * packetLogVolume p +
          (Fintype.card alpha : Real) * packetLogVolume q := by
  rw [packetLogVolume_rescale_eq c hc (tensorPacket p q),
    packetLogVolume_tensor_eq p q, Fintype.card_prod]
  push_cast
  ring

#check packetLogVolume_rescale_eq
#check packetLogVolume_tensor_eq
#check packetLogVolume_rescale_tensor_eq

end LeanFormal.IUT.XiFPaper.Mzk1PacketVolumeConsumerGlueActual
end
