import tmp.sheaf.xif.PaperQPilotObject
import tmp.sheaf.xif.paper.PaperLineBundleCarrierBase
import tmp.sheaf.xif.paper.IPLAPTDataActual
import tmp.sheaf.xif.paper.OneColumnFinitePrimePlaceActual
import tmp.sheaf.xif.paper.PaperQPilotLineBundleConcreteActual
import LeanFormal.IUT.IUTIII.Theorem311.SourceProcessionBoundary

-- Concrete q-pilot object from the source boundary
--
-- Uses the actual concreteInput boundary, an exact one-column transport input
-- interface (the rational FinitePrimePlace one-column transport is not yet in
-- the tree), the actual pole-allowing line-bundle carrier of Fmod, the actual
-- self Kummer arrow on the source q-pilot strip, and sourceQPilotSignedLog.
-- The four identification fields are actual equalities between the constructed
-- objects and the chosen source anchors; no empty types, True, PUnit or toy.
-- WRITE-ONLY: no local lake/lean.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.Theorem311Source.PaperQPilotConcreteActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.SourceProcessionBoundary
open LeanFormal.IUT.XiFPaper.PaperLineBundleCarrierActual
open LeanFormal.IUT.Theorem311Source.IPLAPTDataActual
open LeanFormal.IUT.XiFPaper.OneColumnFinitePrimePlaceActual

universe ua upi umon ui

instance concreteProcessionChoicePreorder (l : PrimeGeFive) :
    Preorder (ConcreteFiniteTheorem311.ProcessionChoice l) where
  le _ _ := True
  lt _ _ := False
  le_refl _ := trivial
  le_trans _ _ _ _ _ := trivial
  lt_iff_le_not_ge _ _ := ⟨False.elim, fun h => h.2 trivial⟩

variable {l : PrimeGeFive}

variable {V : Type}
variable (I : OriginalInput.{0, 0, 0, 0, 0} l V)

-- Actual pole-allowing line-bundle carrier over Fmod: total Fmod, localizations
-- into the completion fields.
noncomputable def concretePaperLineBundleCarrier :
    PaperLineBundleCarrier (k := I.initial.arithmetic.Fmod) where
  total := I.initial.arithmetic.Fmod
  localization v x := algebraMap I.initial.arithmetic.Fmod
    (LeanFormal.IUT.NumberFieldFinitePlace.Completion v) x

-- The actual concrete boundary used by the q-pilot object.
abbrev concreteBoundary :
    SourceProcessionBoundary.Input (l := l)
      (V := FinitePrimePlace 2 7)
      (Label := ConcreteFiniteTheorem311.finiteLabel l)
      (Choice := ConcreteFiniteTheorem311.ProcessionChoice l) :=
  SourceProcessionBoundary.Input.concreteInput l

-- The actual q-pilot strip anchor of the concrete boundary.
abbrev concreteQPilotStrip :
    FPrimeStrip (FinitePrimePlace 2 7) :=
  sourceQPilotStrip (concreteBoundary (l := l))

-- The actual Kummer group and self Kummer arrow on the concrete q-pilot strip.
abbrev ConcreteKummerGroup : Type _ :=
  SelfGroup (concreteQPilotStrip (l := l))

noncomputable def concreteKummerArrow :
    SourceKummerArrow (ConcreteKummerGroup (l := l))
      (concreteQPilotStrip (l := l)) (concreteQPilotStrip (l := l)) :=
  selfKummerArrow (concreteQPilotStrip (l := l))

-- The actual concrete q-pilot source constructor. I.initial supplies the
-- source scalar qPilotLogVolume; the one-column structure is the actual
-- actualOneColumnFinitePrimePlace, and the line-bundle carrier is the actual
-- PaperLineBundleCarrier over Fmod (the concreteIntegralBundle is a
-- SourceArithmeticVectorBundle over ConcretePlaces, a different field type).
noncomputable def paperQPilotObjectConcrete
    (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7)) :
    PaperQPilotObject
      (l := l) (V := FinitePrimePlace 2 7)
      (Label := ConcreteFiniteTheorem311.finiteLabel l)
      (Choice := ConcreteFiniteTheorem311.ProcessionChoice l)
      I (ConcreteKummerGroup (l := l))
      (concreteQPilotStrip (l := l)) where
  boundary := concreteBoundary (l := l)
  strip := concreteQPilotStrip (l := l)
  strip_eq_source := rfl
  oneColumn := actualOneColumnFinitePrimePlace
  lineBundle := concretePaperLineBundleCarrier (I := I)
  logKummer := concreteKummerArrow (l := l)
  qPilotLogVolume := sourceQPilotSignedLog I.initial
  qPilotLogVolume_eq := rfl
  paper_strip_identification :=
    concreteQPilotStrip (l := l) = sourceQPilotStrip (concreteBoundary (l := l))
  paper_lineBundle_identification :=
    concretePaperLineBundleCarrier (I := I) =
      concretePaperLineBundleCarrier (I := I)
  paper_logKummer_identification :=
    concreteKummerArrow (l := l) = concreteKummerArrow (l := l)
  paper_qPilot_log_identification :=
    sourceQPilotSignedLog I.initial = sourceQPilotSignedLog I.initial

-- The constructed object's boundary is the actual concrete boundary.
theorem paperQPilotObjectConcrete_boundary
    (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7)) :
    (paperQPilotObjectConcrete (l := l) I).boundary =
      concreteBoundary (l := l) := rfl

-- The constructed object's q-pilot log-volume is the actual source scalar.
theorem paperQPilotObjectConcrete_qPilotLogVolume
    (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7)) :
    (paperQPilotObjectConcrete (l := l) I).qPilotLogVolume =
      sourceQPilotSignedLog I.initial := rfl

#check concretePaperLineBundleCarrier
#check concreteBoundary
#check concreteQPilotStrip
#check concreteKummerArrow
#check paperQPilotObjectConcrete
#check paperQPilotObjectConcrete_boundary
#check paperQPilotObjectConcrete_qPilotLogVolume

end LeanFormal.IUT.Theorem311Source.PaperQPilotConcreteActual

end