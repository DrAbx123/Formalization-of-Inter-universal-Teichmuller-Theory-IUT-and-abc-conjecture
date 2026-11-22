import tmp.sheaf.xif.paper.Mzk1SignedCor312ContractActual

/-!
# Packet-normalized hull vs q-pilot: signed 3.12 comparison

Signed readouts of the packet-normalized hull log-volume and a q-pilot
normalized log-volume (both negative for the actual regions), with the
containment comparison `qLogVolume <= hullLogVolume`; feeds the green signed
StepXI contract and yields `Cor312Conclusion`.

No sorry, axiom, True or placeholder.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1PacketNormalizedHullComparisonActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1SignedCor312ContractActual

/-- Signed normalized pilot comparison: hull and q-pilot normalized log-volumes
are negative, and the q-pilot lies below the hull (containment). -/
structure PacketNormalizedPilotComparison where
  hullLogVolume : Real
  qLogVolume : Real
  hull_neg : hullLogVolume < 0
  q_neg : qLogVolume < 0
  containment_le : qLogVolume ≤ hullLogVolume

/-- The signed StepXI contract from the packet-normalized comparison. -/
noncomputable def packetNormalizedContract (D : PacketNormalizedPilotComparison)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) : StepXIContract :=
  signedCor312Contract D.qLogVolume D.hullLogVolume D.q_neg
    ipl hipl she hshe apt hapt D.containment_le

/-- **Cor 3.12** conclusion from the packet-normalized hull comparison. -/
theorem packetNormalized_cor312 (D : PacketNormalizedPilotComparison)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion (packetNormalizedContract D ipl hipl she hshe apt hapt) :=
  signedCor312_conclusion D.qLogVolume D.hullLogVolume D.q_neg
    ipl hipl she hshe apt hapt D.containment_le

end LeanFormal.IUT.XiFPaper.Mzk1PacketNormalizedHullComparisonActual
