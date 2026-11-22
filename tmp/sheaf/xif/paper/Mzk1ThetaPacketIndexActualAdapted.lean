/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.IUTII.Theta.FiniteThetaPacket
import LeanFormal.IUT.IUTII.Theta.ThetaLinkAssembly

/-! # IUTII Theta: finite packet / theta-link row index (consumer import point) -/

namespace LeanFormal.IUT.XiFPaper.ThetaPacketIndexActual

/-- Index of the finite-theta-packet / theta-link facts exposed to consumers. -/
def thetaPacketRows : List (String × String) :=
  [ ("FiniteThetaPacket", "structure"),
    ("ThetaLinkAssembly.thetaLink_unitPower", "theorem"),
    ("ThetaLinkAssembly.thetaLink_embeddedUnit", "theorem"),
    ("ThetaLinkAssembly.thetaLink_generator", "theorem"),
    ("ThetaLinkAssembly.thetaLinkSymm_apply", "theorem"),
    ("ThetaLinkAssembly.thetaLink_source_representation", "theorem"),
    ("ThetaLinkAssembly.thetaLink_target_representation", "theorem"),
    ("ThetaLinkAssembly.thetaLink_unique", "theorem"),
    ("ThetaLinkAssembly.thetaLink_unitEquiv_ext", "theorem") ]

theorem thetaPacketRows_length : thetaPacketRows.length = 9 := rfl

end LeanFormal.IUT.XiFPaper.ThetaPacketIndexActual
