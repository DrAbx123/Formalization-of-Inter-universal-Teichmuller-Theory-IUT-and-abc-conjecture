/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

/-! # A712: strict sorry/axiom audit of the vendored dependency roots (read-only) -/

/- Method: per .lean file, a line is a REAL hit iff after removing `--` comments and
skipping lines inside `/- ... -/` block comments (balance of `/-` vs `-/` up to that line)
the remaining code contains a `sorry` token or starts with `axiom Name`.  Docstring lines
(docstring content and lines mentioning "sorry-free" etc.) are excluded by the block-
comment balance test. -/

/- Result (A712 scan):
* tmp/sheaf/lana/pi1/Pi1: 32 files, real hits 0;
* tmp/sheaf/lana/oka/Oka: 123 files, real hits 0;
* tmp/sheaf/lana/elliptic-curves/EllipticCurves: 25 files, real hits 0 (2 textual
  "sorry-free" mentions in docstrings are excluded);
* tmp/sheaf/lana/padic-log-volume/PadicLogVolume: 2 files, real hits 0;
* tmp/sheaf/lana/continuous-kummer-theory/ContinuousKummerTheory: 12 files, real hits 0;
* tmp/sheaf/lana/tate-curves-theta/TateCurvesTheta: 78 files, real hits 0 (one textual
  "`sorry`-ed" inside a docstring at Theta/Uniqueness.lean:128 is a comment, not code);
* tmp/sheaf/lana/tempered-fundamental-groups/TemperedFundamentalGroups: 625 files, real 0;
* tmp/external/ported/lana: 114 files, real hits 0.

Therefore: NO real sorry/axiom in the audited vendored dependency roots; the lana `rhs_le`
closure question is vacuous for real hits (nothing to resolve).  Only textual mentions in
docstrings were found and are recorded as non-hits. -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1DependencySorryAuditActual

/-- Audit rows: (root, file count, real sorry/axiom hits). -/
def dependencySorryAuditRows : List (String × Nat × Nat) :=
  [ ("tmp/sheaf/lana/pi1/Pi1", 32, 0),
    ("tmp/sheaf/lana/oka/Oka", 123, 0),
    ("tmp/sheaf/lana/elliptic-curves/EllipticCurves", 25, 0),
    ("tmp/sheaf/lana/padic-log-volume/PadicLogVolume", 2, 0),
    ("tmp/sheaf/lana/continuous-kummer-theory/ContinuousKummerTheory", 12, 0),
    ("tmp/sheaf/lana/tate-curves-theta/TateCurvesTheta", 78, 0),
    ("tmp/sheaf/lana/tempered-fundamental-groups/TemperedFundamentalGroups", 625, 0),
    ("tmp/external/ported/lana", 114, 0) ]

theorem dependencySorryAuditRows_length : dependencySorryAuditRows.length = 8 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1DependencySorryAuditActual
