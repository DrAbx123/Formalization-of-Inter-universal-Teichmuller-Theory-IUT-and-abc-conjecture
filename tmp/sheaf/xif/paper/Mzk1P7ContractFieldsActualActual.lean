/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1Cor312S3137AssemblyActual
import tmp.sheaf.xif.paper.Mzk1StepXIContractLinkageActual
import Mathlib.Tactic

/-! # P7 #8 CONTRACT linkage: real evidence fields for the StepXI contract. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P7ContractFieldsActualActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312S3137AssemblyActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (P : PaperQPilotObjectActual (l := l) (I := I))

/-- Actual evidence data for the three StepXI contract obligations. -/
structure ContractFieldsActual where
  /-- S3137 q reading is strictly negative: `qPilotLogVolumeReading P < 0`. -/
  q_neg : qPilotLogVolumeReading P < 0
  /-- The log-volume comparison obligation (explicit hypothesis). -/
  comparison : qThetaPilotLogVolumeComparison C3 P
  /-- Signed assembly target: q reading is bounded by the Theta hull reading. -/
  target_bound : qPilotLogVolumeReading P ≤ thetaPilotHullLogVolumeReal C3

/-- The actual evidence object, built from the green S3137 q-positivity and the
(explicit) comparison hypothesis. -/
noncomputable def contractFieldsActualOfComparison
    (h : qThetaPilotLogVolumeComparison C3 P) : ContractFieldsActual C3 P where
  q_neg := by
    change P.signedQPilotLogVolume < 0
    exact P.signedQPilotLogVolume_neg
  comparison := h
  target_bound := h

/-- The actual evidence object is consistent with the signed contract. -/
theorem contractFieldsActual_target_eq (h : qThetaPilotLogVolumeComparison C3 P) :
    (contractFieldsActualOfComparison C3 P h).target_bound = h := rfl

def contractFieldsActualRows : List (String × String × String) :=
  [ ("ContractFieldsActual", "q_nonpos + comparison + target_bound (real evidence)", "CONSTRUCTED"),
    ("contractFieldsActualOfComparison", "actual evidence object from comparison hypothesis", "PROVED (conditional on h)"),
    ("old ContractFieldLink table", "evidence=none historical; NOT evidence", "UNCHANGED") ]

theorem contractFieldsActualRows_length : contractFieldsActualRows.length = 3 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P7ContractFieldsActualActual

end