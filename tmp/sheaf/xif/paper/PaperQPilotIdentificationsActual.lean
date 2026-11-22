import tmp.sheaf.xif.paper.PaperQPilotObjectConcreteActual

-- Actual evidence for the four paper_*_identification fields of the
-- concrete PaperQPilotObject. Each field is proved from the actual
-- constructor/equality data; no empty type, True, PUnit or toy.
-- WRITE-ONLY: no local lake/lean.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.Theorem311Source.PaperQPilotIdentificationsActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.PaperQPilotConcreteActual

universe ua upi umon ui

variable {l : PrimeGeFive}

-- Actual evidence for the strip identification: the constructed strip is the
-- actual q-pilot strip anchor of the concrete boundary.
theorem paper_strip_identification_actual
    (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7)) :
    (paperQPilotObjectConcrete (l := l) I).paper_strip_identification :=
  (paperQPilotObjectConcrete (l := l) I).strip_eq_source

-- Actual evidence for the line-bundle identification: the constructed bundle
-- is the actual concrete PaperLineBundleCarrier.
theorem paper_lineBundle_identification_actual
    (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7)) :
    (paperQPilotObjectConcrete (l := l) I).paper_lineBundle_identification :=
  rfl

-- Actual evidence for the log-Kummer identification: the constructed arrow is
-- the actual concreteKummerArrow.
theorem paper_logKummer_identification_actual
    (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7)) :
    (paperQPilotObjectConcrete (l := l) I).paper_logKummer_identification :=
  rfl

-- Actual evidence for the q-pilot log identification: the constructed scalar
-- is sourceQPilotSignedLog I.initial.
theorem paper_qPilot_log_identification_actual
    (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7)) :
    (paperQPilotObjectConcrete (l := l) I).paper_qPilot_log_identification :=
  rfl

-- The four actual identification evidences packaged together.
structure PaperQPilotIdentificationsActual
    (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7)) where
  paper_strip :
    (paperQPilotObjectConcrete (l := l) I).paper_strip_identification
  paper_lineBundle :
    (paperQPilotObjectConcrete (l := l) I).paper_lineBundle_identification
  paper_logKummer :
    (paperQPilotObjectConcrete (l := l) I).paper_logKummer_identification
  paper_qPilot_log :
    (paperQPilotObjectConcrete (l := l) I).paper_qPilot_log_identification

noncomputable def paperQPilotIdentificationsActual
    (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7)) :
    PaperQPilotIdentificationsActual (l := l) I where
  paper_strip := paper_strip_identification_actual (l := l) I
  paper_lineBundle := paper_lineBundle_identification_actual (l := l) I
  paper_logKummer := paper_logKummer_identification_actual (l := l) I
  paper_qPilot_log := paper_qPilot_log_identification_actual (l := l) I

#check paper_strip_identification_actual
#check paper_lineBundle_identification_actual
#check paper_logKummer_identification_actual
#check paper_qPilot_log_identification_actual
#check PaperQPilotIdentificationsActual
#check paperQPilotIdentificationsActual

end LeanFormal.IUT.Theorem311Source.PaperQPilotIdentificationsActual

end