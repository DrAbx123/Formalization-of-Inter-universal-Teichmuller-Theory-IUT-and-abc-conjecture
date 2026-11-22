/-! # Mzk1VendorCompileStatusActual (stage4 lane; A712 vendor compile-status audit)

A712 (stage4, dependency-tree compile status): statistics for the 7 vendored root
directories and the ported LANA tree — lean files, existing oleans, missing oleans.
Oleans are counted under `.lake/build/lib/lean/<dir>`.  No bulk compilation is done
here (compilation belongs to hull/mainline/watchdog).  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1VendorCompileStatusActual

/-- One vendored-tree row: lean file count, existing oleans, missing oleans. -/
structure VendorRow where
  /-- the vendored directory (repo-relative). -/
  dir : String
  /-- number of .lean files (recursive, excluding .lake). -/
  files : Nat
  /-- number of existing .olean files under .lake/build/lib/lean. -/
  oleans : Nat
  /-- number of missing oleans. -/
  missing : Nat
  deriving Repr, DecidableEq

/-- The A712 vendor compile-status table (counts measured on the current tree). -/
def vendorRows : List VendorRow :=
  [ ⟨"Pi1", 61, 0, 61⟩
  , ⟨"PadicLogVolume", 2, 0, 2⟩
  , ⟨"TateCurvesTheta", 78, 0, 78⟩
  , ⟨"TemperedFundamentalGroups", 625, 0, 625⟩
  , ⟨"Oka", 798, 0, 798⟩
  , ⟨"EllipticCurves", 480, 0, 480⟩
  , ⟨"ContinuousKummerTheory", 18, 18, 0⟩
  , ⟨"tmp/external/ported/lana", 114, 6, 108⟩
  ]

/-- The audit table has eight rows (7 vendored roots + LANA). -/
theorem vendorRows_length : vendorRows.length = 8 := rfl

/-- Every row satisfies `oleans + missing = files` (consistency of the audit). -/
theorem vendorRows_consistent :
    vendorRows.all (fun r => r.oleans + r.missing = r.files) = true := by
  decide

/-- Total lean files across the audited trees. -/
def totalFiles : Nat := vendorRows.foldl (fun acc r => acc + r.files) 0

/-- Total existing oleans across the audited trees. -/
def totalOleans : Nat := vendorRows.foldl (fun acc r => acc + r.oleans) 0

/-- Total missing oleans across the audited trees. -/
def totalMissing : Nat := vendorRows.foldl (fun acc r => acc + r.missing) 0

theorem totalFiles_eq : totalFiles = 2176 := rfl

theorem totalOleans_eq : totalOleans = 24 := rfl

theorem totalMissing_eq : totalMissing = 2152 := rfl

/-- Only `ContinuousKummerTheory` is fully compiled; everything else is uncompiled
(bulk compilation is out of scope for this audit). -/
theorem only_continuousKummerTheory_complete :
    (vendorRows.filter (fun r => r.missing = 0)).map (fun r => r.dir) =
      ["ContinuousKummerTheory"] := by
  decide

#check vendorRows
#check vendorRows_length
#check vendorRows_consistent
#check totalFiles_eq
#check totalOleans_eq
#check totalMissing_eq
#check only_continuousKummerTheory_complete

end LeanFormal.IUT.XiFPaper.Mzk1VendorCompileStatusActual
end
