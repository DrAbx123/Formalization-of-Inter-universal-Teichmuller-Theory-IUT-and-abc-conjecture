/-! # Mzk1VendorRevisionConsistencyV2Actual (stage4 lane; A714 revision consistency V2)

A714 (stage4): re-run of the vendor revision/import consistency audit after the
dependency-tree re-copy.  ROOT COPY vs OLD COPY (`tmp/sheaf/lana/<repo>`): lean file
lists only (no build artifacts), repo prefixes stripped on both sides; SELF-IMPORT
NAME consistency: every `import <Repo>.<Mod>` must resolve to a root-copy `.lean` file.

STATUS AT THIS SNAPSHOT: qpilot's 25-module fix (rev 04ab863a) is STILL IN PROGRESS, so
TemperedFundamentalGroups still has 27 broken import references to 25 missing
`SemistableReduction/` modules.  This V2 file records that honest state; a V3 update
will flip `broken` to 0 once qpilot reports completion.
No bulk compilation.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1VendorRevisionConsistencyV2Actual

/-- One revision row (root copy vs old copy) plus the self-import check. -/
structure RevisionRow where
  repo : String
  newFiles : Nat
  oldFiles : Nat
  onlyNew : Nat
  onlyOld : Nat
  imports : Nat
  broken : Nat
  deriving Repr, DecidableEq

/-- A714 V2 snapshot table (measured on the current tree). -/
def revisionRowsV2 : List RevisionRow :=
  [ ⟨"Pi1", 61, 32, 29, 0, 0, 0⟩
  , ⟨"PadicLogVolume", 2, 2, 0, 0, 0, 0⟩
  , ⟨"TateCurvesTheta", 78, 79, 0, 1, 133, 0⟩
  , ⟨"TemperedFundamentalGroups", 664, 626, 39, 1, 1245, 27⟩
  , ⟨"Oka", 798, 123, 675, 0, 1499, 0⟩
  , ⟨"EllipticCurves", 480, 25, 455, 0, 1136, 0⟩
  , ⟨"ContinuousKummerTheory", 18, 12, 6, 0, 20, 0⟩
  ]

theorem revisionRowsV2_length : revisionRowsV2.length = 7 := rfl

/-- Totals: 4033 self imports, 27 broken in the current snapshot. -/
theorem totalSelfImportsV2_eq :
    revisionRowsV2.foldl (fun acc r => acc + r.imports) 0 = 4033 := rfl

theorem totalBrokenImportsV2_eq :
    revisionRowsV2.foldl (fun acc r => acc + r.broken) 0 = 27 := rfl

/-- All broken imports are in TemperedFundamentalGroups (the other six trees are clean). -/
theorem broken_only_in_TemperedFundamentalGroups :
    (revisionRowsV2.filter (fun r => r.broken ≠ 0)).map (fun r => r.repo) =
      ["TemperedFundamentalGroups"] := by
  decide

/-- qpilot fix status (rev 04ab863a): still pending at this snapshot; when completed,
`totalBrokenImportsV2_eq` must become 0. -/
def qpilotFixStatus : String := "PENDING (25 SemistableReduction modules still missing)"

/-- The 25 missing modules (root paths), to be removed from this list after the fix. -/
def missingModulesV2 : List String :=
  [ "AdmissibleEtaleLift", "AdmissibleLift", "AwayDvd", "CuspInput", "EtaleNil"
  , "EtaleNilStep", "LevelTowerFst", "LevelTowerMk", "LinearProjection"
  , "NilpotentFlatness", "NodeEtaleGlueInput", "NodeEtaleGlueOverlap"
  , "NodeEtaleGlueV0Finite", "NodeEtaleGlueV0Piece", "NodeEtaleGlueV0Tower"
  , "PowFlat", "PowFlatGlue", "TateGlue0", "TateGlue0Cusp", "TateGlue0Tower"
  , "TateGlue1", "TateLevel", "TwoChartPatch", "TwoChartRegular", "ZariskiTwo"
  ]

theorem missingModulesV2_length : missingModulesV2.length = 25 := rfl

#check revisionRowsV2
#check revisionRowsV2_length
#check totalSelfImportsV2_eq
#check totalBrokenImportsV2_eq
#check broken_only_in_TemperedFundamentalGroups
#check missingModulesV2_length

end LeanFormal.IUT.XiFPaper.Mzk1VendorRevisionConsistencyV2Actual
end
