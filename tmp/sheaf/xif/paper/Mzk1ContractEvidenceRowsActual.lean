/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # P7/#6: contract obligation rows (audit-only; no evidence claimed) -/

namespace LeanFormal.IUT.XiFPaper.Mzk1ContractEvidenceRowsActual

def contractRows : List (String × String × String) :=
  [ ("WallObligation.holomorphicHull", "enum only; no StepXIContract field", "NOT-DISCHARGED at contract level") ,
    ("WallObligation.determinantNormalization", "matrixLogDet/packetDet/packetLogVolume_tensorPower green; no contract field", "INTERFACE-ONLY") ,
    ("WallObligation.logVolumeComparison", "qThetaPilotLogVolumeComparison C3 P", "PENDING Audit obligation") ]

theorem contractRows_length : contractRows.length = 3 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1ContractEvidenceRowsActual