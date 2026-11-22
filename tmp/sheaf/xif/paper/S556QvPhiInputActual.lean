import tmp.sheaf.xif.paper.S548SplitFrobenioidActual
import tmp.sheaf.xif.paper.S474Example32GroupLikeIsoActual
import tmp.sheaf.xif.paper.S491AlignedDivisorMapActual
import Iut.Foundations.SourceModelFrobenioidPresentation

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S556QvPhiInputActual

open CategoryTheory
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S432SmallModelActual
open LeanFormal.IUT.XiFPaper.S474Example32GroupLikeIsoActual
open LeanFormal.IUT.XiFPaper.S468DivisorNaturalityActual
open LeanFormal.IUT.XiFPaper.S491AlignedDivisorMapActual
open LeanFormal.IUT.XiFPaper.S522QvPhiRamificationModelActual
open LeanFormal.IUT.XiFPaper.S511PhiCvCandidateActual
open LeanFormal.IUT.XiFPaper.S480Example32InputActual
open LeanFormal.IUT.XiFPaper.S548SplitFrobenioidActual
open Iut.SourceModelFrobenioid

universe u
variable {K : Type u} [Field K]

/-- Conditional data reducing S548: actual rational functions, actual aligned
divisor from an explicit valuation family, only naturality remains assumed. -/
structure S556InputDataActual where
  ramification : RamificationIndexData (K := K)
  valuationFamily : DvSmallValuationFamily (K := K)
  divisor_naturality :
    ∀ {X Y : Example32SmallBase K} (f : X ⟶ Y)
      (value : (example32RationalFunctionsIso (K := K)).obj Y),
      example32DivisorAlignedS491 (K := K) valuationFamily X
          ((example32RationalFunctionsIso (K := K)).pullback f value) =
        (qvPhiRamificationModel (K := K) ramification).gpPullback f
          (example32DivisorAlignedS491 (K := K) valuationFamily Y value)

/-- Actual Input (qvPhi R): rationalFunctions = S474 L^× inclusion; divisor =
S491 aligned valuation map; naturality is the explicit remaining datum. -/
noncomputable def s556InputActual
    (D : S556InputDataActual (K := K)) :
    Input (qvPhiRamificationModel (K := K) D.ramification) where
  rationalFunctions := example32RationalFunctionsIso (K := K)
  divisor := fun X => example32DivisorAlignedS491 (K := K) D.valuationFamily X
  divisor_natural := D.divisor_naturality

/-- Conditional FrobenioidPresentation from S556 actual Input. -/
noncomputable def s556FrobenioidPresentation
    (D : S556InputDataActual (K := K))
    [IsConnected (Example32SmallBase K)]
    (baseTotallyEpimorphic :
      ∀ {X Y : Example32SmallBase K} (f : X ⟶ Y), Epi f) :
    FrobenioidPresentation :=
  SourceModelFrobenioid.Carrier.frobenioidPresentation
    (Phi := qvPhiRamificationModel (K := K) D.ramification)
    (data := s556InputActual (K := K) D) baseTotallyEpimorphic

/-- Exact missing: naturality of the aligned valuation divisor against the
qvPhi ramification pullback. -/
def S556DivisorNaturalityRequired
    (R : RamificationIndexData (K := K))
    (V : DvSmallValuationFamily (K := K)) : Prop :=
  ∀ {X Y : Example32SmallBase K} (f : X ⟶ Y)
    (value : (example32RationalFunctionsIso (K := K)).obj Y),
    example32DivisorAlignedS491 (K := K) V X
        ((example32RationalFunctionsIso (K := K)).pullback f value) =
      (qvPhiRamificationModel (K := K) R).gpPullback f
        (example32DivisorAlignedS491 (K := K) V Y value)

end LeanFormal.IUT.XiFPaper.S556QvPhiInputActual

end
