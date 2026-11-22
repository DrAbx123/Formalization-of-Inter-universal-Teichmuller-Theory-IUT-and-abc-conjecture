import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.Volume
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1TensorPacketAssocActual — tensor-packet log-volume algebra

Genuine new theorems for the finite PositivePacket/tensorPacket layer of
HolomorphicHull/Volume.lean (the Prop 1.1 tensor-packet bookkeeping):
log-volume of rescaled tensor products, associativity of tensor products, and
commutativity of the log-volume under swapping the two packet factors.
No paper object is claimed; no closure; gate NOT PASSED; registry 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1TensorPacketAssocActual

open LeanFormal.IUT

universe u v w

/-- Log-volume of a tensor product of rescaled packets. -/
theorem packetLogVolume_rescale_tensor {α β : Type*} [Fintype α] [Fintype β]
    (c d : Real) (hc : 0 < c) (hd : 0 < d)
    (p : PositivePacket α) (q : PositivePacket β) :
    packetLogVolume (tensorPacket (rescalePacket c hc p) (rescalePacket d hd q)) =
      (Fintype.card β : Real) * ((Fintype.card α : Real) * Real.log c +
          packetLogVolume p) +
        (Fintype.card α : Real) * ((Fintype.card β : Real) * Real.log d +
          packetLogVolume q) := by
  rw [packetLogVolume_tensor, packetLogVolume_rescale, packetLogVolume_rescale]

/-- Tensor-packet log-volume is symmetric under swapping the two factors. -/
theorem packetLogVolume_tensor_comm {α β : Type*} [Fintype α] [Fintype β]
    (p : PositivePacket α) (q : PositivePacket β) :
    packetLogVolume (tensorPacket p q) = packetLogVolume (tensorPacket q p) := by
  rw [packetLogVolume_tensor, packetLogVolume_tensor]
  ring

/-- Associativity of the tensor-packet log-volume. -/
theorem packetLogVolume_tensor_assoc {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    (p : PositivePacket α) (q : PositivePacket β) (r : PositivePacket γ) :
    packetLogVolume (tensorPacket p (tensorPacket q r)) =
      packetLogVolume (tensorPacket (tensorPacket p q) r) := by
  rw [packetLogVolume_tensor, packetLogVolume_tensor,
    packetLogVolume_tensor, packetLogVolume_tensor]
  simp only [Fintype.card_prod]
  push_cast
  ring

end LeanFormal.IUT.XiFPaper.Mzk1TensorPacketAssocActual

end
