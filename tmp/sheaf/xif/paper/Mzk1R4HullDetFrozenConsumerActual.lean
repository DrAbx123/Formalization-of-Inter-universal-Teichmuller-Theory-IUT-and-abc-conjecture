import LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/HullDeterminantLogVolumeReduction
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1R4HullDetFrozenConsumerActual — frozen hull/det spec consumers

Genuine consumers of the R3 hull/determinant frozen specification:
the log-volume of a tensor of rescaled packets is computed from the frozen
log_tensor and log_rescale identities.  No new paper input; no closure;
gate NOT PASSED; registry 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1R4HullDetFrozenConsumerActual

open LeanFormal.IUT

theorem frozenSpec_logVolume_tensor_rescale
    (H : HullDeterminantLogVolumeFrozenSpec)
    {α β : Type*} [Fintype α] [Fintype β]
    (c d : ℝ) (hc : 0 < c) (hd : 0 < d)
    (p : PositivePacket α) (q : PositivePacket β) :
    packetLogVolume (tensorPacket (rescalePacket c hc p) (rescalePacket d hd q)) =
      (Fintype.card β : ℝ) * ((Fintype.card α : ℝ) * Real.log c +
          packetLogVolume p) +
        (Fintype.card α : ℝ) * ((Fintype.card β : ℝ) * Real.log d +
          packetLogVolume q) := by
  rw [H.log_tensor, H.log_rescale, H.log_rescale]
  ring

theorem frozenSpec_logVolume_rescale_rescale
    (H : HullDeterminantLogVolumeFrozenSpec)
    {α : Type*} [Fintype α] (c d : ℝ) (hc : 0 < c) (hd : 0 < d)
    (p : PositivePacket α) :
    packetLogVolume (rescalePacket d hd (rescalePacket c hc p)) =
      (Fintype.card α : ℝ) * Real.log d +
        ((Fintype.card α : ℝ) * Real.log c + packetLogVolume p) := by
  rw [H.log_rescale, H.log_rescale]

end LeanFormal.IUT.XiFPaper.Mzk1R4HullDetFrozenConsumerActual

end
