import tmp.sheaf.xif.paper.S1528UnifiedQPilotObjectActual

/-! # S1548: integration of S1528 unified q-pilot object (lowercase core)

S1528 is the canonical conditional unified object on the lowercase
`tmp.sheaf.xif.paper.PaperQPilotObject` core: actual Ind3Step preorder,
actual `OrigXiFPaperLineBundleCarrier I D` O(-D) line bundle, and the four
concrete/proved identifications.  This file integrates it without importing
the duplicate uppercase `tmp.sheaf.xif.PaperQPilotObject` core (S1479/S1516
legacy), so the environment has exactly one `PaperQPilotObject.lineBundle`.

The only exact gap is `D : OrigXiFPaperLineBundleData I`; no inhabitant of D
is produced and no Nonempty gate is used.  No completion-localized carrier is
used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.S1528Unified
open LeanFormal.IUT.XiFPaper.OrigXiFPaperLineBundle

namespace LeanFormal.IUT.XiFPaper.S1548QPilotIntegrationActual

universe u

variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))

/-- Exact first field for the integration: the actual O(-D) datum D. -/
def S1548DExact
    (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7)) : Type _ :=
  OrigXiFPaperLineBundleData I

/-- S1528's unified object, re-exported as the integrated paper q-pilot
object, conditional on D. -/
noncomputable def s1548UnifiedQPilotObject
    (D : S1548DExact I) :
    PaperQPilotObject (l := l) (V := FinitePrimePlace 2 7)
      (Label := ConcreteFiniteTheorem311.finiteLabel l)
      (Choice := ConcreteFiniteTheorem311.ProcessionChoice l)
      I (OrigXiFPaperSourceKummerGroup l) (OrigXiFPaperSourceStrip l) :=
  s1528UnifiedQPilotObject I D

/-- The integrated object's line-bundle slot is S1480's actual O(-D) carrier. -/
theorem s1548UnifiedQPilotObject_lineBundle
    (D : S1548DExact I) :
    (s1548UnifiedQPilotObject I D).lineBundle =
      OrigXiFPaperLineBundleCarrier I D := rfl

/-- All four identifications hold for the integrated object. -/
theorem s1548UnifiedQPilotObject_identifications
    (D : S1548DExact I) :
    (s1548UnifiedQPilotObject I D).paper_strip_identification ∧
    (s1548UnifiedQPilotObject I D).paper_lineBundle_identification ∧
    (s1548UnifiedQPilotObject I D).paper_logKummer_identification ∧
    (s1548UnifiedQPilotObject I D).paper_qPilot_log_identification :=
  s1528UnifiedQPilotObject_identifications I D

/-- The integrated object's log-volume is the actual bad-place sum. -/
theorem s1548UnifiedQPilotObject_qPilotLogVolume
    (D : S1548DExact I) :
    (s1548UnifiedQPilotObject I D).qPilotLogVolume =
      -OrigXiFPaperBadQAbsLog I.initial :=
  s1528UnifiedQPilotObject_qPilotLogVolume I D

#check @s1548UnifiedQPilotObject
#check @s1548UnifiedQPilotObject_identifications
#print axioms s1548UnifiedQPilotObject
#print axioms s1548UnifiedQPilotObject_identifications

end LeanFormal.IUT.XiFPaper.S1548QPilotIntegrationActual

end
