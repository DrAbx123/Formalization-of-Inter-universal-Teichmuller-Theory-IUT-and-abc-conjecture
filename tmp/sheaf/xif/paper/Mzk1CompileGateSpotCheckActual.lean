/-! # A712 compile-gate spot check (10 green delivery files)

Read-only audit table.  Gate strings were read from `dag/watchdog/logs/*.log`
tails (`#print axioms` last line); the files were NOT recompiled for the sample.
All sampled gates are the allowed trio `[propext, Classical.choice, Quot.sound]`.
Olean flags were checked on disk. -/

structure GateSpotCheckRow where
  file : String
  gate : String
  olean : Bool
  timestamp : String
  deriving Repr

def gateSpotCheckRows : List GateSpotCheckRow :=
  [ { file := "Mzk1PaperFaithfulRouteActual", gate := "propext, Classical.choice, Quot.sound", olean := true, timestamp := "2026-11-11 19:07:17" },
    { file := "Mzk1ObjectTightnessD1Actual", gate := "propext, Classical.choice, Quot.sound", olean := true, timestamp := "2026-11-11 18:10:36" },
    { file := "Mzk1Stage4FinalBoundaryV2AuditActual", gate := "propext, Classical.choice, Quot.sound", olean := true, timestamp := "2026-11-11 17:57:32" },
    { file := "Mzk1Stage4CarrierBadPartAuditActual", gate := "propext, Classical.choice, Quot.sound", olean := true, timestamp := "2026-11-11 17:57:31" },
    { file := "Mzk1HqnegDischargedTCleanGateShaActual", gate := "propext, Classical.choice, Quot.sound", olean := true, timestamp := "2026-11-11 17:57:26" },
    { file := "Mzk1StepXIFinalConditionalABCStatusActual", gate := "propext, Classical.choice, Quot.sound", olean := true, timestamp := "2026-11-11 17:55:59" },
    { file := "Mzk1HullTwoEstimatesPaperShapeActual", gate := "propext, Classical.choice, Quot.sound", olean := true, timestamp := "2026-11-11 17:55:15" },
    { file := "Mzk1BadPartArithmeticV2ShaActual", gate := "propext, Classical.choice, Quot.sound", olean := true, timestamp := "2026-11-11 17:55:10" },
    { file := "Mzk1CorrectedGap2ToABCActual", gate := "propext, Classical.choice, Quot.sound", olean := true, timestamp := "2026-11-11 17:54:29" },
    { file := "Mzk1CorrectedLogLawB3Actual", gate := "propext, Classical.choice, Quot.sound", olean := true, timestamp := "2026-11-11 17:52:54" } ]

theorem gateSpotCheckRows_length : gateSpotCheckRows.length = 10 := rfl

/-- All sampled files have the allowed trio gate and an olean on disk. -/
theorem gateSpotCheckRows_all_trio :
    gateSpotCheckRows.all
      (fun r => r.gate = "propext, Classical.choice, Quot.sound" && r.olean) = true := by
  decide

#print axioms gateSpotCheckRows_all_trio
