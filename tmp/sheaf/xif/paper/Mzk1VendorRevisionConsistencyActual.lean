/-! # Mzk1VendorRevisionConsistencyActual (stage4 lane; A713 vendor revision consistency)

A713 (stage4, version consistency): the 7 vendored trees were re-copied to the repo
root; the old copies remain under `tmp/sheaf/lana/<repo>`.  This audit compares the
root copy with the old copy by LEAN FILE LISTS ONLY (no build artifacts): files,
only-in-root (`onlyNew`), only-in-old (`onlyOld`), and checks self-import NAME
consistency (every `import <Repo>.<Mod>` resolves to a root-copy `.lean` file).

Measured on the current tree (counts are a snapshot).  No bulk compilation is done.
Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1VendorRevisionConsistencyActual

/-- One revision-comparison row. -/
structure RevisionRow where
  /-- the vendored tree. -/
  repo : String
  /-- lean files in the root copy. -/
  newFiles : Nat
  /-- lean files in the old copy (tmp/sheaf/lana/...). -/
  oldFiles : Nat
  /-- files existing only in the root copy. -/
  onlyNew : Nat
  /-- files existing only in the old copy. -/
  onlyOld : Nat
  deriving Repr, DecidableEq

/-- The A713 revision comparison table (normalized by stripping the old-copy repo prefix). -/
def revisionRows : List RevisionRow :=
  [ ⟨"Pi1", 61, 32, 29, 0⟩
  , ⟨"PadicLogVolume", 2, 2, 0, 0⟩
  , ⟨"TateCurvesTheta", 78, 79, 0, 1⟩
  , ⟨"TemperedFundamentalGroups", 664, 626, 39, 1⟩
  , ⟨"Oka", 798, 123, 675, 0⟩
  , ⟨"EllipticCurves", 480, 25, 455, 0⟩
  , ⟨"ContinuousKummerTheory", 18, 12, 6, 0⟩
  ]

/-- The revision table has seven rows. -/
theorem revisionRows_length : revisionRows.length = 7 := rfl

/-- The two old-copy-only files are the old umbrella files. -/
def oldOnlyFiles : List String :=
  [ "TateCurvesTheta/TateCurvesTheta.lean"
  , "TemperedFundamentalGroups/TemperedFundamentalGroups.lean"
  ]

theorem oldOnlyFiles_length : oldOnlyFiles.length = 2 := rfl

/-- Self-import NAME consistency result: total self imports vs broken ones. -/
structure ImportCheckRow where
  /-- the tree. -/
  repo : String
  /-- `import <Repo>.…` lines in the root copy. -/
  imports : Nat
  /-- imports whose target `.lean` file is missing from the root copy. -/
  broken : Nat
  deriving Repr, DecidableEq

/-- The A713 self-import consistency table. -/
def importCheckRows : List ImportCheckRow :=
  [ ⟨"Pi1", 0, 0⟩
  , ⟨"PadicLogVolume", 0, 0⟩
  , ⟨"TateCurvesTheta", 133, 0⟩
  , ⟨"TemperedFundamentalGroups", 1245, 27⟩
  , ⟨"Oka", 1499, 0⟩
  , ⟨"EllipticCurves", 1136, 0⟩
  , ⟨"ContinuousKummerTheory", 20, 0⟩
  ]

theorem importCheckRows_length : importCheckRows.length = 7 := rfl

/-- Totals: 4033 self imports, 27 broken (all in TemperedFundamentalGroups). -/
theorem totalSelfImports_eq :
    importCheckRows.foldl (fun acc r => acc + r.imports) 0 = 4033 := rfl

theorem totalBrokenImports_eq :
    importCheckRows.foldl (fun acc r => acc + r.broken) 0 = 27 := rfl

/-- The 27 broken imports reference 25 missing modules under
`TemperedFundamentalGroups/SemistableReduction/` (not present in the old copy either):
these are files qpilot's copy did not carry over.  Bulk compilation would fail on them. -/
def missingModuleCount : Nat := 25

theorem missingModuleCount_eq : missingModuleCount = 25 := rfl

/-- The missing modules (root paths), recorded for the copy fix. -/
def missingModules : List String :=
  [ "TemperedFundamentalGroups/SemistableReduction/AdmissibleEtaleLift.lean"
  , "TemperedFundamentalGroups/SemistableReduction/AdmissibleLift.lean"
  , "TemperedFundamentalGroups/SemistableReduction/AwayDvd.lean"
  , "TemperedFundamentalGroups/SemistableReduction/CuspInput.lean"
  , "TemperedFundamentalGroups/SemistableReduction/EtaleNil.lean"
  , "TemperedFundamentalGroups/SemistableReduction/EtaleNilStep.lean"
  , "TemperedFundamentalGroups/SemistableReduction/LevelTowerFst.lean"
  , "TemperedFundamentalGroups/SemistableReduction/LevelTowerMk.lean"
  , "TemperedFundamentalGroups/SemistableReduction/LinearProjection.lean"
  , "TemperedFundamentalGroups/SemistableReduction/NilpotentFlatness.lean"
  , "TemperedFundamentalGroups/SemistableReduction/NodeEtaleGlueInput.lean"
  , "TemperedFundamentalGroups/SemistableReduction/NodeEtaleGlueOverlap.lean"
  , "TemperedFundamentalGroups/SemistableReduction/NodeEtaleGlueV0Finite.lean"
  , "TemperedFundamentalGroups/SemistableReduction/NodeEtaleGlueV0Piece.lean"
  , "TemperedFundamentalGroups/SemistableReduction/NodeEtaleGlueV0Tower.lean"
  , "TemperedFundamentalGroups/SemistableReduction/PowFlat.lean"
  , "TemperedFundamentalGroups/SemistableReduction/PowFlatGlue.lean"
  , "TemperedFundamentalGroups/SemistableReduction/TateGlue0.lean"
  , "TemperedFundamentalGroups/SemistableReduction/TateGlue0Cusp.lean"
  , "TemperedFundamentalGroups/SemistableReduction/TateGlue0Tower.lean"
  , "TemperedFundamentalGroups/SemistableReduction/TateGlue1.lean"
  , "TemperedFundamentalGroups/SemistableReduction/TateLevel.lean"
  , "TemperedFundamentalGroups/SemistableReduction/TwoChartPatch.lean"
  , "TemperedFundamentalGroups/SemistableReduction/TwoChartRegular.lean"
  , "TemperedFundamentalGroups/SemistableReduction/ZariskiTwo.lean"
  ]

theorem missingModules_length : missingModules.length = 25 := rfl

#check revisionRows
#check revisionRows_length
#check importCheckRows
#check totalSelfImports_eq
#check totalBrokenImports_eq
#check missingModules_length

end LeanFormal.IUT.XiFPaper.Mzk1VendorRevisionConsistencyActual
end
