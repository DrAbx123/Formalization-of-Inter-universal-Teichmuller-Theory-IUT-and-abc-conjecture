/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.IUTII.Theta.EtaleThetaQuotient

/-! # EtaleThetaQuotient: consumer row index -/

namespace LeanFormal.IUT.XiFPaper.ThetaQuotientIndexActual

def thetaQuotientRows : List (String × String) :=
  [ ("EtaleThetaQuotient.thetaDerivedSubgroup", "abbrev"),
    ("EtaleThetaQuotient.thetaCommutatorKernel", "def"),
    ("EtaleThetaQuotient.thetaCommutatorKernel_le_derivedSubgroup", "theorem"),
    ("EtaleThetaQuotient.ThetaQuotient", "abbrev"),
    ("EtaleThetaQuotient.EllipticAbelianization", "abbrev"),
    ("EtaleThetaQuotient.thetaToElliptic", "def"),
    ("EtaleThetaQuotient.thetaPowerKernel", "def"),
    ("EtaleThetaQuotient.ellipticPowerKernel", "def"),
    ("EtaleThetaQuotient.ModLThetaQuotient", "abbrev"),
    ("EtaleThetaQuotient.modLThetaProjection", "def") ]

theorem thetaQuotientRows_length : thetaQuotientRows.length = 10 := rfl

end LeanFormal.IUT.XiFPaper.ThetaQuotientIndexActual
