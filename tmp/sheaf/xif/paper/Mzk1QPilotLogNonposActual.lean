import tmp.sheaf.xif.PaperQPilotObject
import LeanFormal.IUT.IUTIII.Theorem311.SourceOriginalInput

/-!
# A947: q-pilot signed-log nonpositivity for the paper identification.

sourceQPilotSignedLog S = - sourceBadQAbsLog S, and
sourceBadQAbsLog S = sum_b |log q_b| >= 0; hence the signed q-pilot
log-volume candidate is <= 0.

This file exposes the exact lemmas for the paper_qPilot_log_identification
component needed by abc.  No sorry, axiom or toy witness is used.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1QPilotLogNonposActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source

universe ua uv upi umon ui

variable {l : PrimeGeFive}

/-- The bad q-parameter absolute-log sum is nonnegative. -/
theorem badQAbsLog_nonneg (S : SourceDefinition31Data l) :
    0 ≤ sourceBadQAbsLog S :=
  Theorem311Source.sourceBadQAbsLog_nonneg S

/-- The source q-pilot signed log-volume candidate is nonpositive. -/
theorem sourceQPilotSignedLog_nonpos (S : SourceDefinition31Data l) :
    sourceQPilotSignedLog S ≤ 0 :=
  Theorem311Source.sourceQPilotSignedLog_nonpos S

/-- The same for the initial data of an actual OriginalInput. -/
theorem sourceQPilotSignedLog_nonpos_initial
    {V : Type uv} (I : OriginalInput.{ua, uv, upi, umon, ui} l V) :
    sourceQPilotSignedLog I.initial ≤ 0 :=
  sourceQPilotSignedLog_nonpos I.initial

/-- The nonnegative bad-place absolute-log sum for an actual OriginalInput. -/
theorem badQAbsLog_nonneg_initial
    {V : Type uv} (I : OriginalInput.{ua, uv, upi, umon, ui} l V) :
    0 ≤ sourceBadQAbsLog I.initial :=
  badQAbsLog_nonneg I.initial

end LeanFormal.IUT.XiFPaper.Mzk1QPilotLogNonposActual
