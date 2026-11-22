/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.IUTI.HodgeTheater.HodgeTheaterCore

/-! # IUTI Hodge theater: link-category consumer index -/

namespace LeanFormal.IUT.XiFPaper.HodgeTheaterIndexActual

/-- Index of the Hodge-theater link-category facts exposed to consumers. -/
def hodgeTheaterRows : List (String × String) :=
  [ ("HodgeTheaterCore.HodgeTheater", "structure"),
    ("HodgeTheaterCore.HodgeTheaterLink", "structure"),
    ("HodgeTheaterCore.HodgeTheaterLink.refl", "def"),
    ("HodgeTheaterCore.HodgeTheaterLink.symm", "def"),
    ("HodgeTheaterCore.HodgeTheaterLink.trans", "def"),
    ("HodgeTheaterCore.HodgeTheaterLink.symm_symm", "theorem"),
    ("ConcreteHodgeTheaterExample.gaussianHodgeTheater", "def"),
    ("ConcreteHodgeTheaterExample.gaussianHodgeTheater_q", "theorem"),
    ("ConcreteHodgeTheaterExample.gaussianThreeTheaterSystem", "def") ]

theorem hodgeTheaterRows_length : hodgeTheaterRows.length = 9 := rfl

end LeanFormal.IUT.XiFPaper.HodgeTheaterIndexActual
