import tmp.sheaf.xif.paper.S522QvPhiRamificationModelActual
import Iut.Foundations.SourceModelFrobenioidPresentation
import Iut.Foundations.SourceFrobenioidRationalMonoidTransport

/-! # S548: conditional SplitFrobenioidPresentation over the S522 Phi model

Input data: S522 `qvPhiRamificationModel R`, arbitrary rational functions,
divisor and naturality, joined with connected/totally-epimorphic hypotheses.
Then a CharacteristicSplitting is supplied as an explicit input to build the
actual SplitFrobenioidPresentation.  No splitting is fabricated.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S548SplitFrobenioidActual

open CategoryTheory
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S432SmallModelActual
open LeanFormal.IUT.XiFPaper.S511PhiCvCandidateActual
open LeanFormal.IUT.XiFPaper.S522QvPhiRamificationModelActual
open Iut.SourceModelFrobenioid

universe u
variable {K : Type u} [Field K]

/-- Conditional Input data for the S522 Phi model. -/
structure S548InputData (K : Type u) [Field K] where
  ramification : RamificationIndexData (K := K)
  rationalFunctions :
    GroupLikeAddMonoidOn (Example32SmallBase K) (fun f => IsIso f)
  divisor :
    ∀ X : Example32SmallBase K,
      rationalFunctions.obj X →+
        Algebra.GrothendieckAddGroup ((qvPhiRamificationModel (K := K) ramification).obj X).carrier
  divisor_naturality :
    ∀ {X Y : Example32SmallBase K} (f : X ⟶ Y)
      (value : rationalFunctions.obj Y),
      divisor X (rationalFunctions.pullback f value) =
        (qvPhiRamificationModel (K := K) ramification).gpPullback f (divisor Y value)

/-- Conditional actual Input. -/
noncomputable def s548InputOfData
    (D : S548InputData K) :
    Input (qvPhiRamificationModel (K := K) D.ramification) where
  rationalFunctions := D.rationalFunctions
  divisor := D.divisor
  divisor_natural := D.divisor_naturality

/-- Conditional actual FrobenioidPresentation. -/
noncomputable def s548FrobenioidPresentation
    (D : S548InputData K)
    [IsConnected (Example32SmallBase K)]
    (baseTotallyEpimorphic :
      ∀ {X Y : Example32SmallBase K} (f : X ⟶ Y), Epi f) :
    FrobenioidPresentation :=
  SourceModelFrobenioid.Carrier.frobenioidPresentation
    (Phi := qvPhiRamificationModel (K := K) D.ramification)
    (data := s548InputOfData D) baseTotallyEpimorphic

/-- Conditional SplitFrobenioidPresentation from an explicit characteristic
splitting.  The splitting is an input; no tau is fabricated. -/
noncomputable def s548SplitFrobenioidPresentation
    (D : S548InputData K)
    [IsConnected (Example32SmallBase K)]
    (baseTotallyEpimorphic :
      ∀ {X Y : Example32SmallBase K} (f : X ⟶ Y), Epi f)
    (C : (s548FrobenioidPresentation D baseTotallyEpimorphic).preFrobenioid.CharacteristicSplitting
      (Iut.FrobenioidRationalMonoidTransport.rationalMonoidTransport
        (s548FrobenioidPresentation D baseTotallyEpimorphic))) :
    Iut.SplitFrobenioidPresentation where
  frobenioid := s548FrobenioidPresentation D baseTotallyEpimorphic
  rationalMonoids :=
    Iut.FrobenioidRationalMonoidTransport.rationalMonoidTransport
      (s548FrobenioidPresentation D baseTotallyEpimorphic)
  splittingIndex := ULift.{u+1} Unit
  splittingIndex_nonempty := ⟨ULift.up ()⟩
  splitting := fun _ => C

end LeanFormal.IUT.XiFPaper.S548SplitFrobenioidActual
end
