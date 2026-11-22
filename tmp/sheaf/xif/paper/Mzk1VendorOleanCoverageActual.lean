/-! # Mzk1VendorOleanCoverageActual (stage4 lane; A722 vendor olean coverage)

A722 (stage4): olean coverage audit for the 8 vendored roots (lean files, existing
oleans under .lake/build/lib/lean/<root>, missing oleans).  Measured snapshot; build may
be in progress (compilation belongs to hull/mainline/watchdog).  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1VendorOleanCoverageActual

/-- One vendor olean-coverage row. -/
structure CoverageRow where
  root : String
  files : Nat
  oleans : Nat
  missing : Nat
  deriving Repr, DecidableEq

/-- A722 snapshot: 8 vendored roots. -/
def coverageRows : List CoverageRow :=
  [ ⟨"Pi1", 61, 4, 57⟩
  , ⟨"PadicLogVolume", 2, 0, 2⟩
  , ⟨"TateCurvesTheta", 78, 3, 75⟩
  , ⟨"TemperedFundamentalGroups", 744, 55, 689⟩
  , ⟨"Oka", 798, 0, 798⟩
  , ⟨"EllipticCurves", 480, 0, 480⟩
  , ⟨"ContinuousKummerTheory", 22, 18, 4⟩
  , ⟨"FormalSchemes", 630, 0, 630⟩
  ]

theorem coverageRows_length : coverageRows.length = 8 := rfl

/-- Every row is internally consistent: oleans + missing = files. -/
theorem coverageRows_consistent :
    coverageRows.all (fun r => r.oleans + r.missing = r.files) = true := by
  decide

/-- Total lean files across the 8 vendored roots. -/
def totalFiles : Nat := coverageRows.foldl (fun acc r => acc + r.files) 0

/-- Total existing oleans. -/
def totalOleans : Nat := coverageRows.foldl (fun acc r => acc + r.oleans) 0

/-- Total missing oleans. -/
def totalMissing : Nat := coverageRows.foldl (fun acc r => acc + r.missing) 0

theorem totalFiles_eq : totalFiles = 2815 := rfl

theorem totalOleans_eq : totalOleans = 80 := rfl

theorem totalMissing_eq : totalMissing = 2735 := rfl

/-- Only ContinuousKummerTheory is (nearly) fully compiled; the rest are held back by
the in-progress dependency build. -/
def bestCoveredRoot : String := "ContinuousKummerTheory (18/22 oleans)"

/-- The coverage audit is a snapshot: build state changes as hull/mainline/watchdog
compiles; re-run the counter for a fresh reading. -/
def measurementNote : String :=
  "snapshot; olean build in progress (hull/mainline/watchdog)"

#check coverageRows
#check coverageRows_length
#check coverageRows_consistent
#check totalFiles_eq
#check totalOleans_eq
#check totalMissing_eq
#check bestCoveredRoot

end LeanFormal.IUT.XiFPaper.Mzk1VendorOleanCoverageActual
end
