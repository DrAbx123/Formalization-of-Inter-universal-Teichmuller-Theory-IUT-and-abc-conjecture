/-! # Mzk1VendorOleanCoverageV2Actual (stage4 lane; A724 vendor olean coverage refresh)

A724 (stage4): refreshed olean coverage for the 8 vendored roots (1h20m after A722).
Build progressed: total existing oleans 80 -> 380 (+300), missing 2735 -> 2435.
Snapshot only; compilation belongs to hull/mainline/watchdog.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1VendorOleanCoverageV2Actual

/-- One vendor olean-coverage row (A724 snapshot). -/
structure CoverageRow where
  root : String
  files : Nat
  oleans : Nat
  missing : Nat
  deriving Repr, DecidableEq

/-- A724 refreshed table for the 8 vendored roots. -/
def coverageRows : List CoverageRow :=
  [ ⟨"Pi1", 61, 7, 54⟩
  , ⟨"PadicLogVolume", 2, 2, 0⟩
  , ⟨"TateCurvesTheta", 78, 12, 66⟩
  , ⟨"TemperedFundamentalGroups", 744, 268, 476⟩
  , ⟨"Oka", 798, 47, 751⟩
  , ⟨"EllipticCurves", 480, 25, 455⟩
  , ⟨"ContinuousKummerTheory", 22, 19, 3⟩
  , ⟨"FormalSchemes", 630, 0, 630⟩
  ]

theorem coverageRows_length : coverageRows.length = 8 := rfl

/-- Every row is internally consistent: oleans + missing = files. -/
theorem coverageRows_consistent :
    coverageRows.all (fun r => r.oleans + r.missing = r.files) = true := by
  decide

def totalFiles : Nat := coverageRows.foldl (fun acc r => acc + r.files) 0
def totalOleans : Nat := coverageRows.foldl (fun acc r => acc + r.oleans) 0
def totalMissing : Nat := coverageRows.foldl (fun acc r => acc + r.missing) 0

theorem totalFiles_eq : totalFiles = 2815 := rfl
theorem totalOleans_eq : totalOleans = 380 := rfl
theorem totalMissing_eq : totalMissing = 2435 := rfl

/-- Delta vs A722 snapshot: oleans 80 -> 380 (+300); missing 2735 -> 2435 (-300). -/
def oleanDelta : Nat := 380 - 80
def missingDelta : Nat := 2735 - 2435

theorem oleanDelta_eq : oleanDelta = 300 := rfl
theorem missingDelta_eq : missingDelta = 300 := rfl

/-- Coverage ratio in permille of files compiled (380/2815). -/
def coveragePermille : Nat := 380 * 1000 / 2815

theorem coveragePermille_eq : coveragePermille = 134 := rfl

/-- PadicLogVolume is now fully compiled; ContinuousKummerTheory is 19/22. -/
def fullyCompiledRoots : List String :=
  coverageRows.filterMap (fun r => if r.missing = 0 then some r.root else none)

theorem fullyCompiledRoots_eq : fullyCompiledRoots = ["PadicLogVolume"] := by
  decide

def measurementNote : String :=
  "A724 snapshot; olean build in progress (hull/mainline/watchdog)"

#check coverageRows
#check coverageRows_consistent
#check totalOleans_eq
#check totalMissing_eq
#check oleanDelta_eq
#check coveragePermille_eq
#check fullyCompiledRoots_eq

end LeanFormal.IUT.XiFPaper.Mzk1VendorOleanCoverageV2Actual
end
