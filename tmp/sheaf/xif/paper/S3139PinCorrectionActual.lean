import Mathlib.Tactic

/-!
# S3139: PIN CORRECTION — frozen registry pair is 14041 (data only; correction preserved)

Correction (per lattice/Lead; corrections preserve history, no overwrite):
* Earlier S3139 data/docstrings cite the frozen registry at 13129 (and before that
  13108).  Those references are SUPERSEDED: the CURRENT frozen registry pair is 14041
  (third combined reopen applied):
  - S3131FinalResidualRegistryActual: EXIT=0, SIZE 14041, src sha256 4AF7EC60...,
    olean 5991A075..., checker CITABLE.
  - shehdd single re-pin pending (no registry edits by this stream).
* Affected notes in this stream (historical text kept unchanged; correction recorded
  here): S3139RouteEndgameIdsActual (says 13129), S3139PriorArtReuseIdsActual
  (says 13129), S3139RouteModelIdsActual (says 13129), S3139RouteResidualUpdateV3Actual
  (says 13129), S3139PriorArtAudit2Actual/3Actual docstrings.
* Going forward this stream cites 14041.  lattice recorded the model-route ids in
  S3137ModelRouteIdsNoteActual (with the 14041 correction) and audited the Option-B
  assets: S3133M1ConcretePrimeMatchActual (CITABLE, 5 decls),
  S3135TreeModelBaseUnitScalingActual (CITABLE, 2 decls).
* No registry edits from this stream (frozen 14041, re-pin owned by shehdd/Lead).

**Component, not paper object.**  No sorry/axiom/True/PUnit/toy carrier (data file).
-/

namespace LeanFormal.IUT.XiFPaper.S3139PinCorrectionActual

/-- The current frozen registry pin (as of this record). -/
structure FrozenRegistryPin where
  registrySize : Nat
  sourceSha : String
  oleanSha : String
  checker : String
  note : String

/-- Current frozen registry pair (corrected from the superseded 13129 record). -/
def currentFrozenPin : FrozenRegistryPin :=
  { registrySize := 14041
    sourceSha := "4AF7EC60"
    oleanSha := "5991A075"
    checker := "CITABLE"
    note := "third combined reopen applied; shehdd single re-pin pending" }

/-- The superseded pin value (kept for the correction record). -/
def supersededPinSize : Nat := 13129

/-- The correction: current pin differs from the superseded record. -/
theorem pin_corrected : currentFrozenPin.registrySize ≠ supersededPinSize := by
  decide

end LeanFormal.IUT.XiFPaper.S3139PinCorrectionActual
