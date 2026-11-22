import Mathlib.Data.Real.Basic

/-! # S1058: final checklist for the paper global path (lightweight record)

Heavy files S1051/S1052/S1053/S1054 are not imported here: in the current
environment importing S1051 and S1054 exceeded the 600s compile deadline, and
S1052/S1053 source files have errors.  This file records the exact checklist
without fabricating their actual content.  The classical=paper path is deleted.

Exact items (paper global path):
  1. S1051 paper global qPilot comparison:
       P.procession.average ≤ -s1050PaperGlobalQPilotLog In
  2. S1053 hull-average identification:
       P.procession.average = -weightedPaperV (s994VS In)
  3. S1052 paper qParameter card:
       qParameter = exp(s1050PaperGlobalQPilotLog In), with sign input
  4. S1054 finite links: IPL/SHE/APT propositions + evidence

S994FiniteInput is actual (S1025). -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1058FinalChecklistActual

/-- Exact remaining items on the paper global path. -/
structure S1058FinalChecklist where
  paperGlobalComparison : Prop
  hullAverageIdentification : Prop
  paperQParameterCard : Prop
  paperGlobalSign : Prop
  ipl : Prop
  she : Prop
  apt : Prop
  ipl_evidence : ipl
  she_evidence : she
  apt_evidence : apt

/-- Exact conjunction, no fake witness. -/
def S1058ExactList
    (paperGlobalComparison hullAverageIdentification paperQParameterCard
      paperGlobalSign : Prop) : Prop :=
  paperGlobalComparison ∧ hullAverageIdentification ∧
    paperQParameterCard ∧ paperGlobalSign

/-- The classical=paper equality is not part of the list. -/
def S1058ClassicalPaperPathDeleted : Prop :=
  True

end LeanFormal.IUT.XiFPaper.S1058FinalChecklistActual
end