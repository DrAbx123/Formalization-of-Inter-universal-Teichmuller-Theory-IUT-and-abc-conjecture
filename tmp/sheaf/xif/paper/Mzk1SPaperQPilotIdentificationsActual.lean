/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.OrigXiFPaperQPilotFromSourceLActual
import tmp.sheaf.xif.paper.OrigXiFPaperQPilotObjectActual
import tmp.sheaf.xif.paper.IPLAPTDataActual
import tmp.sheaf.xif.paper.Mzk1A946LineBundleBridgeActual
import tmp.sheaf.xif.paper.Mzk1QPilotLogNonposActual
import Mathlib.Tactic

/-! # A946b: fill the four paper identifications of `OrigXiFPaperQPilotObject` -/

/- The four fields of `OrigXiFPaperQPilotObject` (`OrigXiFPaperQPilotObjectActual:225-232`)
are filled for the green L paper object data using
`OrigXiFPaperStripIdentified_anchor`, `OrigXiFPaperCompletionLineBundleCarrier_identified`
(after the definitional carrier identity), `OrigXiFPaperLogKummerIdentified_of_arrow`,
`sourceQPilotSignedLog_eq_neg_badQAbsLog` and `sourceQPilotSignedLog_nonpos`.
No sorry/axiom. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1SPaperQPilotIdentificationsActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.IPLAPTDataActual
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.OrigXiF
open LeanFormal.IUT.XiFPaper.A946LineBundleBridge
open LeanFormal.IUT.ConcreteFiniteTheorem311
open LeanFormal.IUT.XiFPaper.Mzk1QPilotLogNonposActual
open LeanFormal.IUT.XiFPaper.OrigXiFPaperQPilotFromSourceLActual
open LeanFormal.IUT.XiFPaper.PaperLineBundleCarrierActual
open LeanFormal.IUT.XiFPaper.OneColumnFinitePrimePlaceActual
open LeanFormal.IUT.SourceProcessionBoundary

universe upi umon ui

variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7))

variable (b : OrigXiFQPilotFirstFieldType (l := l))

/-- The actual L paper q-pilot object with all four concrete identifications proved. -/
noncomputable def sPaperQPilotObject :
    OrigXiFPaperQPilotObject (l := l) (V := FinitePrimePlace 2 7)
      (Label := ConcreteFiniteTheorem311.finiteLabel l)
      (Choice := ConcreteFiniteTheorem311.ProcessionChoice l)
      I (SelfGroup (sourceQPilotStrip b)) (sourceQPilotStrip b) where
  boundary := b
  strip := sourceQPilotStrip b
  strip_eq_source := rfl
  oneColumn := actualOneColumnFinitePrimePlace
  lineBundle := OrigXiFSourceLLineBundleCarrier (I := I)
  logKummer := selfKummerArrow (sourceQPilotStrip b)
  qPilotLogVolume := sourceQPilotSignedLog I.initial
  qPilotLogVolume_eq := rfl
  paper_strip_identification := OrigXiFPaperStripIdentified_anchor b
  paper_lineBundle_identification := sourceL_identified (I := I)
  paper_logKummer_identification :=
    OrigXiFPaperLogKummerIdentified_of_arrow (selfKummerArrow (sourceQPilotStrip b))
  paper_qPilot_log_identification :=
    ⟨sourceQPilotSignedLog_eq_neg_badQAbsLog I.initial,
      sourceQPilotSignedLog_nonpos_initial (I := I)⟩

theorem sPaperQPilotObject_qPilotLogVolume :
    (sPaperQPilotObject I b).qPilotLogVolume = sourceQPilotSignedLog I.initial := rfl

theorem sPaperQPilotObject_nonpos : (sPaperQPilotObject I b).qPilotLogVolume ≤ 0 := by
  rw [sPaperQPilotObject_qPilotLogVolume]
  exact sourceQPilotSignedLog_nonpos_initial (I := I)

def sPaperRows : List (String × String) :=
  [ ("paper_strip_identification", "OrigXiFPaperStripIdentified_anchor") ,
    ("paper_lineBundle_identification", "completion carrier identified") ,
    ("paper_logKummer_identification", "OrigXiFPaperLogKummerIdentified_of_arrow") ,
    ("paper_qPilot_log_identification", "signedLog = -badQAbsLog and <= 0") ,
    ("sPaperQPilotObject", "actual L paper object with proved identifications") ]

theorem sPaperRows_length : sPaperRows.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1SPaperQPilotIdentificationsActual
