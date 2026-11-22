/-! # Mzk1VendorOleanCoverageV3Actual (stage4 lane; A796 vendor olean coverage refresh)

A796 (stage4, back to vendor audit routine): refreshed olean coverage for the 8 vendored
roots after the A795 pause.  Totals moved 382 -> 868 oleans since A722/A724 snapshots.
Snapshot only; compilation belongs to hull/mainline/watchdog.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1VendorOleanCoverageV3Actual

structure CoverageRow where
  root : String
  files : Nat
  oleans : Nat
  missing : Nat
  deriving Repr, DecidableEq

/-- A796 refreshed table for the 8 vendored roots. -/
def coverageRows : List CoverageRow :=
  [ ⟨"Pi1", 114, 21, 93⟩
  , ⟨"PadicLogVolume", 2, 2, 0⟩
  , ⟨"TateCurvesTheta", 78, 78, 0⟩
  , ⟨"TemperedFundamentalGroups", 744, 532, 212⟩
  , ⟨"Oka", 828, 113, 715⟩
  , ⟨"EllipticCurves", 480, 25, 455⟩
  , ⟨"ContinuousKummerTheory", 38, 20, 18⟩
  , ⟨"FormalSchemes", 647, 77, 570⟩
  ]

theorem coverageRows_length : coverageRows.length = 8 := rfl

theorem coverageRows_consistent :
    coverageRows.all (fun r => r.oleans + r.missing = r.files) = true := by
  decide

def totalFiles : Nat := coverageRows.foldl (fun acc r => acc + r.files) 0
def totalOleans : Nat := coverageRows.foldl (fun acc r => acc + r.oleans) 0
def totalMissing : Nat := coverageRows.foldl (fun acc r => acc + r.missing) 0

theorem totalFiles_eq : totalFiles = 2931 := rfl
theorem totalOleans_eq : totalOleans = 868 := rfl
theorem totalMissing_eq : totalMissing = 2063 := rfl

/-- Two roots are fully compiled; continuous Kummer theory is 20/38. -/
def fullyCompiledRoots : List String :=
  coverageRows.filterMap (fun r => if r.missing = 0 then some r.root else none)

theorem fullyCompiledRoots_eq :
    fullyCompiledRoots = ["PadicLogVolume", "TateCurvesTheta"] := by
  decide

def measurementNote : String :=
  "A796 snapshot; olean build in progress (hull/mainline/watchdog)"

#check coverageRows
#check coverageRows_consistent
#check totalOleans_eq
#check totalMissing_eq
#check fullyCompiledRoots_eq

end LeanFormal.IUT.XiFPaper.Mzk1VendorOleanCoverageV3Actual
end
