import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.Volume
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1TensorPacketCommutativityActual — determinant symmetry of tensor packets

Genuine new theorem: the determinant of the tensor packet is symmetric under
swapping the two factors.  Reuses the tree packetDet_tensor formula.
No paper object is claimed; no closure; gate NOT PASSED; registry 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1TensorPacketCommutativityActual

open LeanFormal.IUT

theorem packetDet_tensor_comm {α β : Type*} [Fintype α] [Fintype β]
    (p : PositivePacket α) (q : PositivePacket β) :
    packetDet (tensorPacket p q) = packetDet (tensorPacket q p) := by
  rw [packetDet_tensor, packetDet_tensor]
  ring

end LeanFormal.IUT.XiFPaper.Mzk1TensorPacketCommutativityActual

end
