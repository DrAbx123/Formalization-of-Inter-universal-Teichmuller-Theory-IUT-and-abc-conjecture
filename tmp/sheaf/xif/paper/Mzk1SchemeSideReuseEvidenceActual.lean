import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Boundary

/-! # Mzk1SchemeSideReuseEvidenceActual — A475 search evidence for the scheme-side maps gap

A475 exhaustive search: repo "schemeSide"/"SchemeSide" 0 hits; "sectionMap" only
LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Boundary.lean (different semantic object);
"placePoint" only in the external flt-lean tree (unrelated).  This file records the closest
existing asset by name (no copying, no assertion of the missing bridge).  No sorry/axiom. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1SchemeSideReuseEvidenceActual


/-- Row record of the exhaustive-search result. -/
def schemeSideSearchEvidenceRows : List (String × String) :=
  [ ("schemeSide / SchemeSide", "0 hits (A475 decl-index scan)"),
    ("sectionMap", "only SourceDefinition31Boundary.lean:553/557 (different semantics)"),
    ("placePoint", "only external flt-lean tree (unrelated)"),
    ("conclusion", "repo-current missing for the scheme <-> function-field bridge maps") ]

theorem schemeSideSearchEvidenceRows_length : schemeSideSearchEvidenceRows.length = 4 := rfl


end LeanFormal.IUT.XiFPaper.Mzk1SchemeSideReuseEvidenceActual
end
