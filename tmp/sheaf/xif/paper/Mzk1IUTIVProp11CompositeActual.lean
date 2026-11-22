import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.Volume
import tmp.sheaf.xif.paper.Mzk1TensorPacketPositivityActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1IUTIVProp11CompositeActual — IUT IV Prop 1.1 tensor-packet composite

Genuine composite of the finite PositivePacket/tensorPacket layer (Prop 1.1
tensor-packet bookkeeping): determinant and log-volume of the tensor packet,
positivity of the determinant, and the scaling law under rescaling.
No paper object beyond the tree packet API is claimed; no closure; gate NOT
PASSED; registry 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1IUTIVProp11CompositeActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1TensorPacketPositivityActual

theorem iutIVProp11_tensorPacket_composite {α β : Type*} [Fintype α] [Fintype β]
    (p : PositivePacket α) (q : PositivePacket β) :
    (packetDet (tensorPacket p q) =
        packetDet p ^ Fintype.card β * packetDet q ^ Fintype.card α) ∧
      (packetLogVolume (tensorPacket p q) =
        (Fintype.card β : ℝ) * packetLogVolume p +
          (Fintype.card α : ℝ) * packetLogVolume q) ∧
      (0 < packetDet (tensorPacket p q)) ∧
      (∀ (c : ℝ) (hc : 0 < c), packetDet (rescalePacket c hc p) =
        c ^ Fintype.card α * packetDet p) :=
  ⟨packetDet_tensor p q, packetLogVolume_tensor p q,
   packetDet_tensor_pos p q, fun c hc => packetDet_rescale c hc p⟩

end LeanFormal.IUT.XiFPaper.Mzk1IUTIVProp11CompositeActual

end
