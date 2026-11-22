import tmp.sheaf.xif.paper.OrigXiFPaperQPilotObjectPreorderActual
import tmp.sheaf.xif.paper.S1679CompleteODCarrierActual
import tmp.sheaf.xif.paper.S1487OQPilotScalarEqualityActual

/-! # S1680: full PaperQPilotObject with the S1679 O(-D) line bundle

Layer: O/F bridge object.  Builds the frozen `PaperQPilotObject` on the
concrete S1487 faithful input C with:
* boundary := SourceProcessionBoundary.Input.concreteInput;
* strip := sourceQPilotStrip boundary;
* oneColumn := actualOneColumnFinitePrimePlace;
* lineBundle := s1679Carrier (actual complete O(-D) carrier, not a native
  donor D, S1423Module, free lattice or completion carrier);
* logKummer := selfKummerArrow (actual supplied kappa-orbit action);
* qPilotLogVolume := sourceQPilotSignedLog I.initial.

The four paper_*_identification fields are concrete propositions and are
proved from the S1479/S1528 identification lemmas and S1679's line-bundle
identification.  No fake carrier or Nonempty gate.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1680QPilotObjectActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1487OQPilotScalarEqualityActual
open LeanFormal.IUT.XiFPaper.OneColumnFinitePrimePlaceActual
open LeanFormal.IUT.XiFPaper.OrigXiF
open LeanFormal.IUT.XiFPaper.OrigXiF.OrigXiFPaperQPilotObjectActual
open LeanFormal.IUT.XiFPaper.S1679CompleteODCarrierActual

variable {l : PrimeGeFive}

/-- The same concrete faithful input C used by S1487/S1527/S1650. -/
abbrev S1680Input : OriginalInput.{0, 0, 0, 0, 0} l S1487W :=
  S1487FaithfulInput (l := l)

/-- Full paper q-pilot object with the S1679 complete O(-D) carrier. -/
noncomputable def s1680QPilotObject :
    PaperQPilotObject (l := l) (V := FinitePrimePlace 2 7)
      (Label := ConcreteFiniteTheorem311.finiteLabel l)
      (Choice := ConcreteFiniteTheorem311.ProcessionChoice l)
      (S1680Input (l := l)) (OrigXiFPaperSourceKummerGroup l)
      (OrigXiFPaperSourceStrip l) where
  boundary := OrigXiFPaperSourceBoundary l
  strip := OrigXiFPaperSourceStrip l
  strip_eq_source := rfl
  oneColumn := actualOneColumnFinitePrimePlace
  lineBundle := s1679Carrier l
  logKummer := OrigXiFPaperSourceKummerArrow l
  qPilotLogVolume := sourceQPilotSignedLog (S1680Input (l := l)).initial
  qPilotLogVolume_eq := rfl
  paper_strip_identification :=
    OrigXiFPaperStripIdentified (OrigXiFPaperSourceBoundary l)
      (OrigXiFPaperSourceStrip l)
  paper_lineBundle_identification :=
    S1679PaperLineBundleIdentified l
  paper_logKummer_identification :=
    OrigXiFPaperLogKummerIdentified (OrigXiFPaperSourceKummerArrow l)
  paper_qPilot_log_identification :=
    OrigXiFPaperQPilotScalarIdentified (S1680Input (l := l)).initial
      (sourceQPilotSignedLog (S1680Input (l := l)).initial)

/-- The object's strip identification holds. -/
theorem s1680_paper_strip :
    (s1680QPilotObject (l := l)).paper_strip_identification :=
  OrigXiFPaperStripIdentified_anchor (OrigXiFPaperSourceBoundary l)

/-- The object's line-bundle identification is S1679's actual O(-D) carrier
identification. -/
theorem s1680_paper_lineBundle :
    (s1680QPilotObject (l := l)).paper_lineBundle_identification :=
  s1679_identified l

/-- The object's log-Kummer identification holds. -/
theorem s1680_paper_logKummer :
    (s1680QPilotObject (l := l)).paper_logKummer_identification :=
  OrigXiFPaperLogKummerIdentified_of_arrow (OrigXiFPaperSourceKummerArrow l)

/-- The object's q-pilot scalar identification holds. -/
theorem s1680_paper_qPilot_log :
    (s1680QPilotObject (l := l)).paper_qPilot_log_identification :=
  ⟨sourceQPilotSignedLog_eq_neg_badQAbsLog (S1680Input (l := l)).initial,
    sourceQPilotSignedLog_nonpos (S1680Input (l := l)).initial⟩

end LeanFormal.IUT.XiFPaper.S1680QPilotObjectActual

end
