import LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/HullDeterminantLogVolumeReduction
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1R4HullDetAssemblyActual — hull+det assembly at the packet level

Genuine composite of the R3 hull/determinant assets: the matrix log-determinant
of the tensor packet and of the rescaled packet, obtained by combining the
matrix log-determinant laws with the packet tensor/rescale laws.
No new paper input; no closure; gate NOT PASSED; registry 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1R4HullDetAssemblyActual

open LeanFormal.IUT

theorem matrixLogDet_packetDiagonalMatrix_tensor {α β : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (p : PositivePacket α) (q : PositivePacket β) :
    matrixLogDet (packetDiagonalMatrix (tensorPacket p q)) =
      (Fintype.card β : ℝ) * matrixLogDet (packetDiagonalMatrix p) +
        (Fintype.card α : ℝ) * matrixLogDet (packetDiagonalMatrix q) := by
  rw [← packetLogVolume_eq_matrixLogDet (tensorPacket p q), packetLogVolume_tensor,
    ← packetLogVolume_eq_matrixLogDet p, ← packetLogVolume_eq_matrixLogDet q]

theorem matrixLogDet_packetDiagonalMatrix_rescale {label : Type*} [Fintype label]
    [DecidableEq label] (c : ℝ) (hc : 0 < c) (p : PositivePacket label) :
    matrixLogDet (packetDiagonalMatrix (rescalePacket c hc p)) =
      (Fintype.card label : ℝ) * Real.log c +
        matrixLogDet (packetDiagonalMatrix p) := by
  rw [← packetLogVolume_eq_matrixLogDet (rescalePacket c hc p),
    packetLogVolume_rescale, ← packetLogVolume_eq_matrixLogDet p]

end LeanFormal.IUT.XiFPaper.Mzk1R4HullDetAssemblyActual

end
