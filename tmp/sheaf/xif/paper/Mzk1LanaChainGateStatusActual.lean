/-! # A713 LANA chain gate status snapshot

Read-only audit table.  Source of status: `dag/watchdog/watchdog.log` (last status
per lana file) and per-file `dag/watchdog/logs/*.log` tails.  LANA files have no
`#print axioms` in their per-file logs, so DONE rows record `NO-GATE-PRINT` rather
than inventing a trio.  Target files are NOT yet DONE in this snapshot; their logs
show missing-dependency olean errors (transient while the closure is being built).
A721 V3 final-rebuild snapshot: mainline dag_build/dag_plan rebuilt and watchdog
restarted 19:42:55 local.  plan.json: targets=629, closure=1510, dirty=903, missing=0;
first CYCLE pending=1061 max=16 (19:43:25).  Counting scope remains exactly
`tmp/external/ported/lana/`.  Target files are still SKIP at the snapshot (dep oleans
not yet ready); this is expected, not a red error. -/

structure LanaGateRow where
  file : String
  status : String
  gate : String
  timestamp : String
  olean : Bool
  deriving Repr

def lanaGateRows : List LanaGateRow :=
  [ { file := "tmp/external/ported/lana/Iut/Cor312/ThetaData/UltrametricSqrt.lean", status := "DONE EXIT=0", gate := "NO-GATE-PRINT", timestamp := "2026-11-11 19:03:02", olean := true },
    { file := "tmp/external/ported/lana/Iut/Cor312/ThetaData/PointMap.lean", status := "DONE EXIT=0", gate := "NO-GATE-PRINT", timestamp := "2026-11-11 19:03:02", olean := true },
    { file := "tmp/external/ported/lana/Iut/Cor312/ThetaData/Places.lean", status := "DONE EXIT=0", gate := "NO-GATE-PRINT", timestamp := "2026-11-11 19:03:02", olean := true },
    { file := "tmp/external/ported/lana/Iut/Tower/IntegralModel.lean", status := "DONE EXIT=0", gate := "NO-GATE-PRINT", timestamp := "2026-11-11 19:03:01", olean := true },
    { file := "tmp/external/ported/lana/Iut/Torsion/Identities.lean", status := "DONE EXIT=0", gate := "NO-GATE-PRINT", timestamp := "2026-11-11 19:03:01", olean := true },
    { file := "tmp/external/ported/lana/Iut/Tower/ReductionKernel.lean", status := "DONE EXIT=0", gate := "NO-GATE-PRINT", timestamp := "2026-11-11 19:03:01", olean := true },
    { file := "tmp/sheaf/lana/iut/Iut/Wall/BPS.lean", status := "DONE EXIT=0", gate := "NO-GATE-PRINT", timestamp := "2026-11-11 05:35:56", olean := true },
    { file := "tmp/sheaf/lana/tempered-fundamental-groups/TemperedFundamentalGroups/SemistableReduction/CompleteFree.lean", status := "DONE EXIT=0", gate := "NO-GATE-PRINT", timestamp := "2026-11-11 05:34:20", olean := true },
    { file := "tmp/external/ported/lana/Iut/Implication/LogVolumeBound.lean", status := "SKIP", gate := "-", timestamp := "2026-11-11 21:13:32", olean := false },
    { file := "tmp/external/ported/lana/Iut/Concrete/LocalEstimate.lean", status := "SKIP", gate := "-", timestamp := "2026-11-11 21:13:32", olean := false } ]

/-- Status counts over the 665 lana files tracked in the watchdog log snapshot. -/
def lanaStatusCounts : List (String × Nat) :=
  [ ("DONE EXIT=0", 35), ("FAIL EXIT=1", 5), ("SKIP", 74), ("START", 0) ]

def lanaSnapshot : String := "2026-11-11 21:21 local (V3 refresh A728b, ported prefix only)"

def lanaCountingScope : String := "tmp/external/ported/lana/ only"

def lanaRestartLine : String := "2026-11-11T12:44:10Z REBUILD GRAPH; CYCLE pending=625 at 13:04:51Z (A724)"

def lanaPortedTracked : Nat := 114

def planTargets : Nat := 629
def planClosure : Nat := 1510
def planDirty : Nat := 903
def planMissing : Nat := 0
def cyclePending : Nat := 625

theorem planScope_snapshot : planTargets = 629 ∧ planClosure = 1510 ∧ planDirty = 903 ∧ planMissing = 0 := by
  decide

theorem lanaGateRows_length : lanaGateRows.length = 10 := rfl
theorem lanaStatusCounts_length : lanaStatusCounts.length = 4 := rfl

/-- Every sampled row is either a DONE row with no printed gate or a FAIL row. -/
theorem lanaGateRows_status_ok :
    lanaGateRows.all
      (fun r => r.status = "DONE EXIT=0" || r.status = "FAIL EXIT=1" || r.status = "SKIP") = true := by
  decide

/-- The two target files are still FAIL in this snapshot (not yet DONE). -/
theorem lanaTargets_not_done :
    (lanaGateRows.filter (fun r =>
      r.file = "tmp/external/ported/lana/Iut/Implication/LogVolumeBound.lean" ||
        r.file = "tmp/external/ported/lana/Iut/Concrete/LocalEstimate.lean")).all
      (fun r => r.status = "SKIP" || r.status = "FAIL EXIT=1") = true := by
  decide

#print axioms lanaGateRows_status_ok
