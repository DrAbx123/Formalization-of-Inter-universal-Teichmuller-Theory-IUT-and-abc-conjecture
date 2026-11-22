import tmp.sheaf.xif.paper.S550QvPhiPreFrobenioidActual
import Iut.Foundations.SourceModelFrobenioidPresentation

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S557QvPhiSplitFrobenioidConditional

open CategoryTheory
open Iut
open Iut.SourceModelFrobenioid
open LeanFormal.IUT.XiFPaper.S432SmallModelActual
open LeanFormal.IUT.XiFPaper.S511PhiCvCandidateActual
open LeanFormal.IUT.XiFPaper.S522QvPhiRamificationModelActual
open LeanFormal.IUT.XiFPaper.S550QvPhiPreFrobenioidActual

universe u
variable {K : Type u} [Field K]
variable (R : RamificationIndexData (K := K))
variable (data : Input (qvPhi (K := K) R))
variable (Tau : QvPhiTauData (K := K) R data)

/-- Conditional CharacteristicSplitting from the S550 transport and tau data. -/
noncomputable def qvCharacteristicSplitting :
    (qvPreFrobenioid (K := K) R data).CharacteristicSplitting
      (qvRationalMonoidTransport (K := K) R data) :=
  characteristicSplittingOfTauData (K := K) R data Tau

/-- Conditional FrobenioidPresentation, with connectedness and total epimorphicity. -/
noncomputable def qvFrobenioidPresentation
    [IsConnected (Example32SmallBase K)]
    (baseTotallyEpimorphic :
      ∀ {X Y : Example32SmallBase K} (f : X ⟶ Y), Epi f) :
    FrobenioidPresentation :=
  SourceModelFrobenioid.Carrier.frobenioidPresentation
    (Phi := qvPhi (K := K) R) (data := data) baseTotallyEpimorphic

/-- Conditional SplitFrobenioidPresentation. -/
noncomputable def qvSplitFrobenioidPresentation
    [IsConnected (Example32SmallBase K)]
    (baseTotallyEpimorphic :
      ∀ {X Y : Example32SmallBase K} (f : X ⟶ Y), Epi f) :
    SplitFrobenioidPresentation where
  frobenioid := qvFrobenioidPresentation (K := K) R data baseTotallyEpimorphic
  rationalMonoids := qvRationalMonoidTransport (K := K) R data
  splittingIndex := PUnit
  splittingIndex_nonempty := ⟨PUnit.unit⟩
  splitting := fun _ => qvCharacteristicSplitting (K := K) R data Tau

end LeanFormal.IUT.XiFPaper.S557QvPhiSplitFrobenioidConditional

end
