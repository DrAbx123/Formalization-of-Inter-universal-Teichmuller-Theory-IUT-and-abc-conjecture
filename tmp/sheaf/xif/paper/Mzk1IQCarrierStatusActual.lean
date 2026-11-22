/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # P7/#2: IQ carrier status table (audit data, no construction claimed) -/

namespace LeanFormal.IUT.XiFPaper.Mzk1IQCarrierStatusActual

def iqCarrierStatus : List (String × String × String) :=
  [ ("A481 restricted product construction", "GREEN", "A481LiteralIQCarrierActual.lean:17") ,
    ("literal IQ(S+; n, D^vdash) carrier type/identification", "MISSING", "IQCarrierFromSource.lean:6/42; LiteralIQCarrierActual.lean:6/19/96") ,
    ("C3 IQ carrier vs source reduced IQ packet", "GAP", "C3IQActualPacketGapActual.lean:54") ,
    ("C6 IQ carrier (not literal)", "CLUE", "ConcretePaperSignedHullActual.lean:14; GlobalThetaPilotIQKummerActual.lean:61") ]

theorem iqCarrierStatus_length : iqCarrierStatus.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1IQCarrierStatusActual