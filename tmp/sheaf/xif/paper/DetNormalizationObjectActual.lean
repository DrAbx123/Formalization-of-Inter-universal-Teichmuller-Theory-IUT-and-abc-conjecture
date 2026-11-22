/- Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. -/
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.HullDeterminantLogVolumeReduction

/-! Det-normalization object built by reusing HullDeterminantLogVolumeReduction
(matrixLogDet, packetLogVolume, packetDet and their proved determinant laws). -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.DetNormalizationObjectActual

open LeanFormal.IUT
open scoped BigOperators Kronecker

universe u v w

/-- The packet det-normalized log-volume: the log-determinant of the packet's
diagonal matrix. -/
noncomputable def packetDetLogVolume {label : Type u} [Fintype label]
    [DecidableEq label] (packet : PositivePacket label) : Real :=
  matrixLogDet (packetDiagonalMatrix packet)

theorem packetDetLogVolume_constructed {label : Type u} [Fintype label]
    [DecidableEq label] (packet : PositivePacket label) :
    packetDetLogVolume packet = matrixLogDet (packetDiagonalMatrix packet) := rfl

theorem packetDetLogVolume_eq_packetLogVolume {label : Type u} [Fintype label]
    [DecidableEq label] (packet : PositivePacket label) :
    packetDetLogVolume packet = packetLogVolume packet :=
  (packetLogVolume_eq_matrixLogDet packet).symm

theorem packetDetLogVolume_eq_log_packetDet {label : Type u} [Fintype label]
    [DecidableEq label] (packet : PositivePacket label) :
    packetDetLogVolume packet = Real.log (packetDet packet) :=
  (packetLogVolume_eq_matrixLogDet packet).symm.trans
    (packetLogVolume_eq_log_det packet)

theorem packetDetLogVolume_tensor {alpha : Type u} {beta : Type v}
    [Fintype alpha] [Fintype beta] [DecidableEq alpha] [DecidableEq beta]
    (p : PositivePacket alpha) (q : PositivePacket beta) :
    packetDetLogVolume (tensorPacket p q) =
      (Fintype.card beta : Real) * packetDetLogVolume p +
        (Fintype.card alpha : Real) * packetDetLogVolume q := by
  unfold packetDetLogVolume
  rw [packetDiagonalMatrix_tensor,
    matrixLogDet_kronecker_posDef (packetDiagonalMatrix_posDef p)
      (packetDiagonalMatrix_posDef q)]

theorem packetDiagonalMatrix_rescale {label : Type u} [Fintype label]
    [DecidableEq label] (c : Real) (hc : 0 < c) (packet : PositivePacket label) :
    packetDiagonalMatrix (rescalePacket c hc packet) =
      c • packetDiagonalMatrix packet := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [packetDiagonalMatrix, rescalePacket, Matrix.diagonal, Matrix.smul_apply]
  · simp [packetDiagonalMatrix, rescalePacket, Matrix.diagonal, Matrix.smul_apply, h]

theorem packetDetLogVolume_rescale {label : Type u} [Fintype label]
    [DecidableEq label] (c : Real) (hc : 0 < c) (packet : PositivePacket label) :
    packetDetLogVolume (rescalePacket c hc packet) =
      (Fintype.card label : Real) * Real.log c + packetDetLogVolume packet := by
  unfold packetDetLogVolume
  rw [packetDiagonalMatrix_rescale,
    matrixLogDet_smul_posDef c hc (packetDiagonalMatrix_posDef packet)]

/-- The det-normalization object: the packet, its determinant and the
det-normalized log-volume, with constructed equalities. -/
structure DetNormalizationObject (label : Type u) [Fintype label] [DecidableEq label] where
  packet : PositivePacket label
  detValue : Real
  detValue_eq : detValue = packetDet packet
  detLogVolume : Real
  detLogVolume_eq : detLogVolume = packetDetLogVolume packet

noncomputable def detNormalizationObject (label : Type u) [Fintype label]
    [DecidableEq label] (packet : PositivePacket label) :
    DetNormalizationObject label where
  packet := packet
  detValue := packetDet packet
  detValue_eq := rfl
  detLogVolume := packetDetLogVolume packet
  detLogVolume_eq := rfl

theorem detNormalizationObject_constructed (label : Type u) [Fintype label]
    [DecidableEq label] (packet : PositivePacket label) :
    (detNormalizationObject label packet).detValue = packetDet packet ∧
    (detNormalizationObject label packet).detLogVolume = packetDetLogVolume packet := by
  refine ⟨rfl, rfl⟩

end LeanFormal.IUT.XiFPaper.DetNormalizationObjectActual