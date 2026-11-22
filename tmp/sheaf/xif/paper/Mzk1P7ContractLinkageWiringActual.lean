/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1Cor312S3137AssemblyActual
import tmp.sheaf.xif.paper.Mzk1P7ContractFieldsActualActual
import Mathlib.Tactic

/-! # P7 #8: StepXI contract with real evidence (replaces True fields) -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P7ContractLinkageWiringActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.Mzk1XiFFormalStepActual
open LeanFormal.IUT.XiFPaper.Mzk1P7ContractFieldsActualActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (P : PaperQPilotObjectActual (l := l) (I := I))

/-- StepXI contract built from the **actual evidence** object: the three fields
carry the comparison/q-positivity propositions with their proofs, not `True`. -/
noncomputable def contractOfContractFieldsActual
    (E : ContractFieldsActual C3 P) : StepXIContract where
  qSigned := qPilotLogVolumeReading P
  thetaSigned := thetaPilotHullLogVolumeReal C3
  targetSigned := qPilotLogVolumeReading P
  q_negative := E.q_neg
  ipl := qThetaPilotLogVolumeComparison C3 P
  she := qPilotLogVolumeReading P ≤ 0
  apt := qPilotLogVolumeReading P ≤ thetaPilotHullLogVolumeReal C3
  ipl_evidence := E.comparison
  she_evidence := E.q_neg.le
  apt_evidence := E.target_bound
  q_le_target := le_rfl
  target_le_theta := E.comparison

/-- Cor 3.12 from the actual evidence object (only the comparison is a hypothesis). -/
theorem cor312_of_contractFieldsActual (E : ContractFieldsActual C3 P) :
    Cor312Conclusion (contractOfContractFieldsActual C3 P E) :=
  xi_f_formal_step E.comparison

/-- The evidence-carrying contract is definitionally the comparison contract at the
signed data level. -/
theorem contractOfContractFieldsActual_qSigned (E : ContractFieldsActual C3 P) :
    (contractOfContractFieldsActual C3 P E).qSigned = qPilotLogVolumeReading P := rfl

def contractLinkageWiringRows : List (String × String × String) :=
  [ ("contractOfContractFieldsActual", "StepXI contract with real ipl/she/apt evidence", "CONSTRUCTED"),
    ("cor312_of_contractFieldsActual", "Cor312 from real evidence object", "PROVED"),
    ("contractOfContractFieldsActual_qSigned", "signed data compatibility", "PROVED (rfl)") ]

theorem contractLinkageWiringRows_length : contractLinkageWiringRows.length = 3 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P7ContractLinkageWiringActual

end