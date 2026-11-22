import tmp.sheaf.xif.paper.S3136OldSplitPointUnitRegionWiringActual
import tmp.sheaf.xif.paper.S3136OldAttemptHonestyAuditActual

/-! # S3131 reuse: old hunit PROVED with actual D0 + honesty -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S3131OldHunitDReuseActual

def S3131OldHunitDReuse : List (String × String) :=
  [ ("S2722HunitDActual:34 S2722D0 = max 0 (unitVol - hullVol); :41 nonneg; :44 S2722_hunitD; :68 S2722_gap2_with_D0", "hunit PROVED with ACTUAL D0; gap-2 reduction with hunit discharged -> REUSE via lgpOldHunitD/lgpOldSplit/lgpOldGap2WithD0"),
    ("S2720BridgeHaarActual:70 normalizedRegion_logVolume_le_split", "hsplit producer -> REUSE"),
    ("S2590SingletonNull", "hptfin by singleton-null; hpoint DEGENERATE (do not use as paper evidence)"),
    ("S3136OldAttemptHonestyAuditActual (8 rows)", "honesty audit: bridge conditional ABC-strength; hval refuted; hweightvol open; hpoint degenerate; dictionary unconditional only in degenerate carrier") ]

theorem S3131OldHunitDReuse_length : S3131OldHunitDReuse.length = 4 := rfl

-- #check (prior-art name to verify later): lgpOldHunitD
-- #check (prior-art name to verify later): lgpOldSplit
-- #check (prior-art name to verify later): lgpOldGap2WithD0

end LeanFormal.IUT.XiFPaper.S3131OldHunitDReuseActual
end