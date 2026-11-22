import tmp.sheaf.xif.paper.OrigXiFPaperBoundaryStripActual
import tmp.sheaf.xif.paper.OneColumnFinitePrimePlaceActual
import tmp.sheaf.xif.PaperQPilotObject
import LeanFormal.IUT.IUTIII.Theorem311.SourceProcessionBoundary

/-! # OrigXiF paper q-pilot components (no qside assembly)

This file supplies the four data components of a paper q-pilot object

  boundary, strip, oneColumn, lineBundle

without assembling the qside PaperQPilotObject itself (the assembly is left
to the qside consumer).  The concrete finite source case uses:

* actual boundary: SourceProcessionBoundary.Input.concreteInput l;
* actual strip: sourceQPilotStrip boundary;
* actual one-column structure: actualOneColumnFinitePrimePlace;
* actual pole-allowing line-bundle carrier: s1457LineBundle.

No PUnit carrier, empty type, arbitrary Set, True, or axiom is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.OrigXiFPaperQPilotComponentsActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.SourceProcessionBoundary
open LeanFormal.IUT.XiFPaper.PaperLineBundleCarrierActual
open LeanFormal.IUT.XiFPaper.OneColumnFinitePrimePlaceActual
open LeanFormal.IUT.NumberFieldFinitePlace

universe upi umon ui

variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7))

/-- Actual pole-allowing completion carrier on the rational finite places of
the source base field. -/
noncomputable def origXiFComponentsLineBundle :
    PaperLineBundleCarrier (k := I.initial.arithmetic.Fmod) where
  total := (v : NumberField.FinitePlace I.initial.arithmetic.Fmod) →
    NumberFieldFinitePlace.Completion v
  localization := fun v f => f v

/-- The four data components of the OrigXiF paper q-pilot, without the
PaperQPilotObject qside assembly. -/
structure OrigXiFPaperQPilotComponents where
  /-- Actual source procession boundary. -/
  boundary : SourceProcessionBoundary.Input (l := l)
    (V := FinitePrimePlace 2 7)
    (Label := ConcreteFiniteTheorem311.finiteLabel l)
    (Choice := ConcreteFiniteTheorem311.ProcessionChoice l)
  /-- Actual source q-pilot strip anchor. -/
  strip : FPrimeStrip (FinitePrimePlace 2 7)
  /-- Strip is definitionally the source q-pilot strip of the boundary. -/
  strip_eq_source : strip = sourceQPilotStrip boundary
  /-- Actual one-column arithmetic holomorphic structure. -/
  oneColumn : SourceOneColumnArithmeticHolomorphicStructure
    (FinitePrimePlace 2 7)
  /-- Actual pole-allowing paper line-bundle carrier over the source base field. -/
  lineBundle : PaperLineBundleCarrier (k := I.initial.arithmetic.Fmod)

/-- Actual OrigXiF paper q-pilot components in the concrete finite source case. -/
noncomputable def origXiFPaperQPilotComponents :
    OrigXiFPaperQPilotComponents (l := l) I where
  boundary := SourceProcessionBoundary.Input.concreteInput l
  strip := sourceQPilotStrip (SourceProcessionBoundary.Input.concreteInput l)
  strip_eq_source := rfl
  oneColumn := actualOneColumnFinitePrimePlace
  lineBundle := origXiFComponentsLineBundle (I := I)

/-- The constructed boundary is the actual concrete source boundary. -/
theorem origXiFPaperQPilotComponents_boundary :
    (origXiFPaperQPilotComponents (l := l) I).boundary =
      SourceProcessionBoundary.Input.concreteInput l := rfl

/-- The constructed strip is the actual source q-pilot strip. -/
theorem origXiFPaperQPilotComponents_strip :
    (origXiFPaperQPilotComponents (l := l) I).strip =
      sourceQPilotStrip (SourceProcessionBoundary.Input.concreteInput l) := rfl

/-- The constructed strip identification holds definitionally. -/
theorem origXiFPaperQPilotComponents_strip_eq_source :
    (origXiFPaperQPilotComponents (l := l) I).strip =
      sourceQPilotStrip (origXiFPaperQPilotComponents (l := l) I).boundary := rfl

/-- The constructed one-column structure is the actual finite-prime-place one. -/
theorem origXiFPaperQPilotComponents_oneColumn :
    (origXiFPaperQPilotComponents (l := l) I).oneColumn =
      actualOneColumnFinitePrimePlace := rfl

/-- The constructed line-bundle carrier is the actual pole-allowing completion
carrier. -/
theorem origXiFPaperQPilotComponents_lineBundle :
    (origXiFPaperQPilotComponents (l := l) I).lineBundle =
      origXiFComponentsLineBundle (I := I) := rfl

/-- The line-bundle carrier is not an empty type: its total space contains zero. -/
theorem origXiFPaperQPilotComponents_lineBundle_total_nonempty :
    Nonempty (origXiFPaperQPilotComponents (l := l) I).lineBundle.total :=
  ⟨fun _ => 0⟩

end LeanFormal.IUT.XiFPaper.OrigXiFPaperQPilotComponentsActual

end
