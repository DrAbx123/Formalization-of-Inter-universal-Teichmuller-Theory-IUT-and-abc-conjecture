/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # P7: partial-discharge status list (audit-only) -/

namespace LeanFormal.IUT.XiFPaper.Mzk1P7PartialStatusActual

def partialItems : List (String × String) :=
  [ ("#2 paper IQ carrier", "A481 restricted product green; literal IQ identification missing") ,
    ("#3 (Ob3-3) source identification", "S3134 det law + WeightedDet profile scaling; source identification missing") ,
    ("#5 theta raw Haar vs paper normalized V", "raw = [C3 block:Q_p] * candidateNormalizedV; paper V/C3-D identifications missing") ]

theorem partialItems_length : partialItems.length = 3 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P7PartialStatusActual