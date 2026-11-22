import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.Volume
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1TensorPacketPositivityActual — positivity of tensor-packet determinants

Genuine new positivity theorems for the finite PositivePacket/tensorPacket layer:
packetDet is positive, tensor products preserve positivity of the determinant,
and rescaling preserves determinant positivity.  Reuses the tree packet API.
No paper object is claimed; no closure; gate NOT PASSED; registry 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1TensorPacketPositivityActual

open LeanFormal.IUT

theorem packetDet_pos {label : Type*} [Fintype label] (packet : PositivePacket label) :
    0 < packetDet packet := by
  rw [packetDet_eq_prod]
  exact Finset.prod_pos (fun i _ => packet.positive i)

theorem packetDet_ne_zero {label : Type*} [Fintype label]
    (packet : PositivePacket label) : packetDet packet ≠ 0 :=
  ne_of_gt (packetDet_pos packet)

theorem packetDet_tensor_pos {α β : Type*} [Fintype α] [Fintype β]
    (p : PositivePacket α) (q : PositivePacket β) :
    0 < packetDet (tensorPacket p q) := by
  rw [packetDet_tensor]
  exact mul_pos (pow_pos (packetDet_pos p) _) (pow_pos (packetDet_pos q) _)

theorem packetDet_rescale_pos {label : Type*} [Fintype label]
    (c : Real) (hc : 0 < c) (packet : PositivePacket label) :
    0 < packetDet (rescalePacket c hc packet) := by
  rw [packetDet_rescale]
  exact mul_pos (pow_pos hc _) (packetDet_pos packet)

end LeanFormal.IUT.XiFPaper.Mzk1TensorPacketPositivityActual

end
