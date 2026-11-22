import tmp.sheaf.xif.paper.OneColumnFinitePrimePlaceActual
import LeanFormal.IUT.IUTIII.Theorem311.SourceH1H2Construction

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S1205StageToLocalConcreteGapActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.OneColumnFinitePrimePlaceActual

/-- Concrete actual local field at a finite-prime place: the rational completion. -/
abbrev ConcreteStageLocalField (v : FinitePrimePlace 2 7) : Type :=
  NumberFieldFinitePlace.Completion (finitePrimePlaceToQ v)

/-- Concrete actual local ring at a finite-prime place: completed valuation integers. -/
abbrev ConcreteStageLocalRing (v : FinitePrimePlace 2 7) : Type :=
  NumberFieldFinitePlace.CompletionIntegers (finitePrimePlaceToQ v)

theorem concreteStageLocalField_eq (v : FinitePrimePlace 2 7) :
    ConcreteStageLocalField v = NumberFieldFinitePlace.Completion (finitePrimePlaceToQ v) := rfl

theorem concreteStageLocalRing_eq (v : FinitePrimePlace 2 7) :
    ConcreteStageLocalRing v =
      NumberFieldFinitePlace.CompletionIntegers (finitePrimePlaceToQ v) := rfl

/-- If a source stage-place assignment exists, the concrete local-field family is
actual. -/
def concreteStageLocalFieldOfPlace
    (n : Nat) (stagePlace : Fin (n + 1) → FinitePrimePlace 2 7) :
    Fin (n + 1) → Type :=
  fun i => ConcreteStageLocalField (stagePlace i)

def concreteStageLocalRingOfPlace
    (n : Nat) (stagePlace : Fin (n + 1) → FinitePrimePlace 2 7) :
    Fin (n + 1) → Type :=
  fun i => ConcreteStageLocalRing (stagePlace i)

end LeanFormal.IUT.XiFPaper.S1205StageToLocalConcreteGapActual

end
