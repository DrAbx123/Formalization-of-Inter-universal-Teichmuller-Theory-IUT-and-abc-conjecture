import tmp.sheaf.xif.paper.GenEll21GeometricCoreConsumerActual

/-! # Mzk1ProblemDApplicabilityReuseActual — reuse of the existing applicability input

A475: exhaustive repository search shows Problem D applicability already exists as the abbrev
ProblemDApplicabilityInput in GenEll21GeometricCoreConsumerActual.lean:93.  This file records
the reuse (alias + definitional equivalence) instead of creating a duplicate target.  No
sorry/axiom.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1ProblemDApplicabilityReuseActual

open LeanFormal.IUT.XiFPaper.GenEll21GeometricCoreConsumerActual

attribute [local instance] Classical.decEq

/-- Alias of the existing Problem D applicability input (reuse, not a new object). -/
abbrev ProblemDApplicabilityInputReuse : Prop := ProblemDApplicabilityInput

/-- The alias is definitionally the existing input. -/
theorem problemDApplicabilityInputReuse_iff :
    ProblemDApplicabilityInputReuse ↔ ProblemDApplicabilityInput :=
  Iff.rfl

/-- Row record: reuse evidence. -/
def problemDApplicabilityReuseRows : List (String × String) :=
  [ ("ProblemDApplicabilityInputReuse", "REUSE: GenEll21GeometricCoreConsumerActual.lean:93"),
    ("problemDApplicabilityInputReuse_iff", "PROVED (rfl)") ]

theorem problemDApplicabilityReuseRows_length :
    problemDApplicabilityReuseRows.length = 2 := rfl

#check ProblemDApplicabilityInputReuse
#check problemDApplicabilityInputReuse_iff

end LeanFormal.IUT.XiFPaper.Mzk1ProblemDApplicabilityReuseActual
end
