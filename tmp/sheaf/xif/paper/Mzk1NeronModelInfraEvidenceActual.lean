import Mathlib

/-! # Mzk1NeronModelInfraEvidenceActual — A475 search evidence for NeronModelInfra

A475 correction: NeronModelInfra assets DO exist in the repo, in
tmp/external/flt-lean/Definitions/Def_NeronModelInfra_OmegaMinimalComponentData.lean
(ComponentReading, MinimalComponentData, IsOmegaMinimal, ...).  The external tree is not on
the lake search path for this project, so this file records the reuse evidence only.
The earlier "0 matches repo-wide" claim is retracted.  No sorry/axiom. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1NeronModelInfraEvidenceActual

/-- Row record of A475 NeronModelInfra evidence (correction of an earlier PARK). -/
def neronModelInfraEvidenceRows : List (String × String) :=
  [ ("NeronModelInfra", "tmp/external/flt-lean/Definitions/Def_NeronModelInfra_OmegaMinimalComponentData.lean:19+"),
    ("ComponentReading / MinimalComponentData / IsOmegaMinimal", "same external file"),
    ("import status", "external tree not on lake search path; adaptation requires module wiring"),
    ("earlier claim", "retracted: not repo-wide missing (A475 correction)") ]

theorem neronModelInfraEvidenceRows_length : neronModelInfraEvidenceRows.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1NeronModelInfraEvidenceActual
end
