/-! # A739 LANA chain gate status V4 (root Iut scope)

New scope per Lead A739: the current watchdog target is the repository-root `Iut/`
tree (950 files) plus its vendor dependency prefixes.  Old records under
`tmp/sheaf/lana_latest/` and `tmp/external/ported/lana/` are historical and are NOT
used for this table.  LANA per-file logs have no `#print axioms`, so DONE rows record
`NO-GATE-PRINT`.  Snapshot: 2026-11-11 21:43 local. -/

structure LanaV4Row where
  file : String
  status : String
  gate : String
  timestamp : String
  deriving Repr

def lanaV4Rows : List LanaV4Row :=
  [ { file := "Iut/Abc/Classical.lean", status := "DONE EXIT=0", gate := "NO-GATE-PRINT", timestamp := "2026-11-11 21:41:12" },
    { file := "Iut/Tripod/Legendre.lean", status := "DONE EXIT=0", gate := "NO-GATE-PRINT", timestamp := "2026-11-11 21:41:12" },
    { file := "Iut/Concrete/LocalConstruct/LocalLogShell.lean", status := "DONE EXIT=0", gate := "NO-GATE-PRINT", timestamp := "2026-11-11 21:42:31" },
    { file := "Iut/Cor312/ThetaData/PointMap.lean", status := "DONE EXIT=0", gate := "NO-GATE-PRINT", timestamp := "2026-11-11 21:42:00" },
    { file := "Iut/Cor312/ThetaData/Places.lean", status := "DONE EXIT=0", gate := "NO-GATE-PRINT", timestamp := "2026-11-11 21:42:37" },
    { file := "Iut/Torsion/Identities.lean", status := "DONE EXIT=0", gate := "NO-GATE-PRINT", timestamp := "2026-11-11 21:42:31" },
    { file := "Iut/Anabelian/Model.lean", status := "DONE EXIT=0", gate := "NO-GATE-PRINT", timestamp := "2026-11-11 21:42:52" },
    { file := "Iut/Wall/EtaAlg.lean", status := "PENDING", gate := "-", timestamp := "-" },
    { file := "Iut/Wall/Checks.lean", status := "PENDING", gate := "-", timestamp := "-" },
    { file := "Iut/MainTheorem.lean", status := "PENDING", gate := "-", timestamp := "-" },
    { file := "Iut/Implication/Theorem110.lean", status := "PENDING", gate := "-", timestamp := "-" } ]

/-- Root-Iut subset counts in the current cycle (tracked=14). -/
def rootIutCounts : List (String × Nat) :=
  [ ("DONE EXIT=0", 7), ("START", 7) ]

/-- Vendor-subset counts (tracked=900). -/
def vendorCounts : List (String × Nat) :=
  [ ("DONE EXIT=0", 387), ("FAIL EXIT=1", 78), ("SKIP", 403), ("START", 32) ]

def planClosureV4 : Nat := 1422
def planDirtyV4 : Nat := 1039

theorem lanaV4Rows_length : lanaV4Rows.length = 11 := rfl
theorem rootIutCounts_length : rootIutCounts.length = 2 := rfl
theorem vendorCounts_length : vendorCounts.length = 4 := rfl

theorem lanaV4Rows_statuses_ok :
    lanaV4Rows.all (fun r => r.status = "DONE EXIT=0" || r.status = "PENDING") = true := by
  decide

theorem planScopeV4 : planClosureV4 = 1422 ∧ planDirtyV4 = 1039 := by
  decide

#print axioms lanaV4Rows_statuses_ok
