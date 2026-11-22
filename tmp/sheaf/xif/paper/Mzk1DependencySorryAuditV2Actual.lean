/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

/-! # A713: strict sorry/axiom audit V2, root-level vendored dependency trees -/

/- Method (same as A712, plus token-level confirmation): a line counts as a REAL code hit
only if after removing `--` comments it matches one of:
  `:= sorry` / `exact sorry` / `apply sorry` / `refine sorry` / `by sorry` (line-final), or
  `axiom Name : ...` / `private axiom Name : ...` at declaration position.
Docstring prose (e.g. lines starting with the word `axiom is ...`, or `sorry` inside
backticks) is therefore excluded.  Both filters agree: no real hit. -/

/- Root-level trees (copied by lead from the 7 dependency sources):
* Pi1/: 61 files, 0 real;
* PadicLogVolume/: 2 files, 0 real;
* TateCurvesTheta/: 78 files, 0 real (one `sorry`-ed docstring prose at
  Theta/Uniqueness.lean:128);
* TemperedFundamentalGroups/: 664 files, 0 real — this includes the 12 new modules
  fetched from GitHub rev 04ab863a (raw.githubusercontent; provenance marker below);
* Oka/: 798 files, 0 real (all `axiom` occurrences are docstring prose);
* EllipticCurves/: 480 files, 0 real (one `axiom in the form ...` docstring at
  FormalGroup/LogAdditivity.lean:259);
* ContinuousKummerTheory/: 18 files, 0 real.

Old vendored copies (A712) remain 0 real: tmp/sheaf/lana/{pi1/Pi1, oka/Oka,
elliptic-curves/EllipticCurves, padic-log-volume/PadicLogVolume,
continuous-kummer-theory/ContinuousKummerTheory, tate-curves-theta/TateCurvesTheta,
tempered-fundamental-groups/TemperedFundamentalGroups} and tmp/external/ported/lana.

Conclusion: 0 real sorry/axiom in both the root-level 7 trees and the 12 newly fetched
TemperedFundamentalGroups modules; no resolution needed, lana `rhs_le` closure unaffected. -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1DependencySorryAuditV2Actual

/-- Root-tree audit rows: (root, file count, real hits). -/
def rootDependencyAuditRows : List (String × Nat × Nat) :=
  [ ("Pi1", 61, 0),
    ("PadicLogVolume", 2, 0),
    ("TateCurvesTheta", 78, 0),
    ("TemperedFundamentalGroups", 664, 0),
    ("Oka", 798, 0),
    ("EllipticCurves", 480, 0),
    ("ContinuousKummerTheory", 18, 0) ]

/-- Provenance note for the 12 newly fetched TemperedFundamentalGroups modules. -/
def tfgNewModulesProvenance : String :=
  "raw.githubusercontent GitHub rev 04ab863a (12 modules, copied into root TemperedFundamentalGroups/)"

theorem rootDependencyAuditRows_length : rootDependencyAuditRows.length = 7 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1DependencySorryAuditV2Actual
