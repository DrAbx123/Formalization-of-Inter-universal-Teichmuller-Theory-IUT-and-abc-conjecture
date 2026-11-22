import tmp.sheaf.xif.paper.PaperQPilotObjectConcreteActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Actual q-pilot F-prime-strip target for the concrete PaperQPilotObject

This file constructs the concrete q-pilot F-prime-strip target from the actual
source boundary and the actual source q-pilot strip:

  concreteBoundary := SourceProcessionBoundary.Input.concreteInput l;
  concreteQPilotStrip := sourceQPilotStrip concreteBoundary.

The target records the actual F-prime-strip, its definitional identification
with sourceQPilotStrip concreteBoundary, and the actual forgetful D-prime-strip.
The concrete PaperQPilotObject's strip is then identified with this target by
actual equality.

No empty type, True, PUnit, arbitrary equivalence, axiom, or sorry is used.
-/

noncomputable section

namespace LeanFormal.IUT.Theorem311Source.PaperQPilotStripTargetActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SourceProcessionBoundary
open LeanFormal.IUT.Theorem311Source.PaperQPilotConcreteActual

universe ua upi umon ui

variable {l : PrimeGeFive}

variable (I : OriginalInput.{ua, 0, upi, umon, ui} l (FinitePrimePlace 2 7))

/-- The actual concrete source boundary. -/
abbrev targetConcreteBoundary :
    SourceProcessionBoundary.Input (l := l)
      (V := FinitePrimePlace 2 7)
      (Label := ConcreteFiniteTheorem311.finiteLabel l)
      (Choice := ConcreteFiniteTheorem311.ProcessionChoice l) :=
  concreteBoundary (l := l)

/-- The actual q-pilot F-prime-strip target of a source boundary, with its
actual forgetful D-prime-strip. -/
structure PaperQPilotStripTarget
    (boundary : SourceProcessionBoundary.Input (l := l)
      (V := FinitePrimePlace 2 7)
      (Label := ConcreteFiniteTheorem311.finiteLabel l)
      (Choice := ConcreteFiniteTheorem311.ProcessionChoice l)) where
  strip : FPrimeStrip (FinitePrimePlace 2 7)
  strip_eq : strip = sourceQPilotStrip boundary
  dStrip : DPrimeStrip (FinitePrimePlace 2 7)
  dStrip_eq : dStrip = strip.toDPrimeStrip

/-- The actual concrete q-pilot strip target. -/
noncomputable def concreteQPilotStripTarget :
    PaperQPilotStripTarget (targetConcreteBoundary (l := l)) where
  strip := sourceQPilotStrip (targetConcreteBoundary (l := l))
  strip_eq := rfl
  dStrip := (sourceQPilotStrip (targetConcreteBoundary (l := l))).toDPrimeStrip
  dStrip_eq := rfl

/-- The target strip is the actual source q-pilot strip. -/
theorem concreteQPilotStripTarget_strip :
    (concreteQPilotStripTarget (l := l)).strip =
      sourceQPilotStrip (targetConcreteBoundary (l := l)) :=
  rfl

/-- The target F-prime-strip identification with the concrete source strip. -/
theorem concreteQPilotStripTarget_identification :
    (concreteQPilotStripTarget (l := l)).strip =
      concreteQPilotStrip (l := l) :=
  rfl

/-- The target D-prime-strip is the actual forgetful image of its F-prime-strip. -/
theorem concreteQPilotStripTarget_dStrip_eq :
    (concreteQPilotStripTarget (l := l)).dStrip =
      (concreteQPilotStripTarget (l := l)).strip.toDPrimeStrip :=
  rfl

/-- The concrete PaperQPilotObject's strip is the concrete target strip. -/
theorem paperQPilotObjectConcrete_strip_eq_target :
    (paperQPilotObjectConcrete (l := l) I).strip =
      (concreteQPilotStripTarget (l := l)).strip :=
  rfl

/-- The concrete PaperQPilotObject's actual strip identification holds: its
strip equals the source q-pilot strip. -/
theorem paperQPilotObjectConcrete_strip_identification :
    (paperQPilotObjectConcrete (l := l) I).strip =
      sourceQPilotStrip (concreteBoundary (l := l)) :=
  rfl

/-- The concrete PaperQPilotObject's strip identification field is the actual
identification of the constructed target. -/
theorem paperQPilotObjectConcrete_paper_strip_identification :
    (paperQPilotObjectConcrete (l := l) I).paper_strip_identification :=
  rfl

end LeanFormal.IUT.Theorem311Source.PaperQPilotStripTargetActualAdapted

end
