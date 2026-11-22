/-! Mainline: A475 repo-search evidence record (Mathlib-only; documentation data).
  Each row: search term, hit count, scope, conclusion.
  Scopes: LeanFormal (LF), tmp Lean files (TMP), Mathlib (ML), coord docs (DOC).
  Purpose: evidence that the named inputs are NAMED in repo, not "needing breakthroughs". -/

namespace LeanFormal.IUT.XiFPaper.Mzk1RepoSearchEvidenceActualAdapted

/-- (term, hit count, scope, conclusion). -/
def repoSearchEvidence : List (String × Nat × String × String) :=
  [ ("f4b", 0, "LF", "no f4b lemma in LeanFormal; tmp has gap statement file (Mzk1StepProviderGapStatementsActual)"),
    ("fixedBetaChoice", 3, "TMP", "only gap statement/adaptation files; named interface StepProviderFixedBetaChoiceInput"),
    ("schemeSideMaps", 0, "LF", "no exact identifier; generic sectionMap exists (265 hits) in InitialTheta"),
    ("sectionMap", 265, "LF", "generic section maps in InitialTheta; no scheme-side bridge construction"),
    ("placePoint", 110, "TMP", "placePoint statements exist in tmp consumer files; no construction"),
    ("ProblemDApplicability", 38, "TMP", "GenEll21 consumer statements exist; not green"),
    ("HTLink", 20, "TMP", "HodgeTheater transport law statements exist"),
    ("bothSided", 6, "TMP", "Hull13 both-sided statement/inputs exist (Mzk1Hull13BothSidedBaseActual)"),
    ("arbitraryIterate", 6, "TMP", "H7/Ob9 arbitrary-iterate named in consumer file"),
    ("Ominus", 2, "TMP", "H5 O(-)^{-1} named-input placeholder only") ]

theorem repoSearchEvidence_length : repoSearchEvidence.length = 10 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1RepoSearchEvidenceActualAdapted