/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.IUTII.Frobenioid.Example36FrobenioidTransport
import tmp.sheaf.xif.paper.Mzk1FrobeniusUnitsTransportActual

/-! # Example36 Frobenius transport: global-unit map consumer index -/

namespace LeanFormal.IUT.XiFPaper.FrobeniusUnitsIndexActual

/-- Index of the global-unit transport facts exposed to consumers. -/
def frobeniusUnitsRows : List (String × String) :=
  [ ("Example36FrobenioidTransport.unitsMapOfRingHom", "def"),
    ("Example36FrobenioidTransport.unitsMapOfRingHom_apply_coe", "theorem"),
    ("Example36FrobenioidTransport.unitsMapOfRingHom_one", "theorem"),
    ("Example36FrobenioidTransport.unitsMapOfRingHom_mul", "theorem"),
    ("Example36FrobenioidTransport.unitsMapOfRingHom_pow", "theorem"),
    ("Example36FrobenioidTransport.unitsMapOfRingHom_id", "theorem"),
    ("Mzk1FrobeniusUnitsTransportActual.unitsMapOfRingHom_comp", "theorem"),
    ("Mzk1FrobeniusUnitsTransportActual.unitsMapOfRingHom_injective", "theorem"),
    ("Mzk1FrobeniusUnitsTransportActual.unitsMapOfRingHom_comp_assoc", "theorem"),
    ("Mzk1FrobeniusUnitsTransportActual.unitsMapOfRingHom_zpow", "theorem"),
    ("Mzk1FrobeniusUnitsTransportActual.unitsMapOfRingHom_congr", "theorem") ]

theorem frobeniusUnitsRows_length : frobeniusUnitsRows.length = 11 := rfl

end LeanFormal.IUT.XiFPaper.FrobeniusUnitsIndexActual
