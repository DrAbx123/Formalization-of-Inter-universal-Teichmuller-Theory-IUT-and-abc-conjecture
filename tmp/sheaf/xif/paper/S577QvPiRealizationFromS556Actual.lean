import tmp.sheaf.xif.paper.S564QvPiOtriangleCandidateActual
import tmp.sheaf.xif.paper.S556QvPhiInputActual
import tmp.sheaf.xif.paper.S438QVFamilyKSideCandidateActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S577QvPiRealizationFromS556Actual

open CategoryTheory
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S432SmallModelActual
open LeanFormal.IUT.XiFPaper.S474Example32GroupLikeIsoActual
open LeanFormal.IUT.XiFPaper.S511PhiCvCandidateActual
open LeanFormal.IUT.XiFPaper.S522QvPhiRamificationModelActual
open LeanFormal.IUT.XiFPaper.S556QvPhiInputActual
open LeanFormal.IUT.XiFPaper.S550QvPhiPreFrobenioidActual
open LeanFormal.IUT.XiFPaper.S564QvPiOtriangleCandidateActual
open LeanFormal.IUT.XiFPaper.S438QVFamilyKSideCandidateActual
open Iut.SourceModelFrobenioid

universe u
variable {K : Type u} [Field K]
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- A q_v π rational function inside the S556 actual Input. -/
structure S556QvPiData (D : S556InputDataActual (K := K)) where
  A : Object (qvPhi D.ramification)
  rationalFunction : (example32RationalFunctionsIso (K := K)).obj A.base
  divisor_eq :
    (s556InputActual (K := K) D).divisor A.base rationalFunction =
      Algebra.GrothendieckAddGroup.of (ULift.up (qVFamilyK T b).order)

/-- Conditional QvPiRealization built from S556 Input and S556QvPiData. -/
noncomputable def qvPiRealizationOfS556
    (D : S556InputDataActual (K := K)) (P : S556QvPiData (K := K) T b D) :
    QvPiRealization (K := K) T b D.ramification (s556InputActual (K := K) D) :=
  { A := P.A
    rationalFunction := P.rationalFunction
    divisor_eq := P.divisor_eq }

theorem qvPiEndomorphismOfS556_divisor
    (D : S556InputDataActual (K := K)) (P : S556QvPiData (K := K) T b D) :
    (qvPiEndomorphism (K := K) T b D.ramification
      (s556InputActual (K := K) D)
      (qvPiRealizationOfS556 (K := K) T b D P)).hom.divisor =
      ULift.up (qVFamilyK T b).order := rfl

/-- Exact required datum: an S556 rational function whose aligned divisor is
the qVFamilyK order. -/
def S556QvPiRequired
    (D : S556InputDataActual (K := K)) : Prop :=
  Nonempty (S556QvPiData (K := K) T b D)

theorem s556QvPiRequired_iff
    (D : S556InputDataActual (K := K)) :
    S556QvPiRequired (K := K) T b D ↔
      ∃ (A : Object (qvPhi D.ramification))
        (r : (example32RationalFunctionsIso (K := K)).obj A.base),
        (s556InputActual (K := K) D).divisor A.base r =
          Algebra.GrothendieckAddGroup.of (ULift.up (qVFamilyK T b).order) := by
  constructor
  · rintro ⟨P⟩
    exact ⟨P.A, P.rationalFunction, P.divisor_eq⟩
  · rintro ⟨A, r, hr⟩
    exact ⟨{ A := A, rationalFunction := r, divisor_eq := hr }⟩

end LeanFormal.IUT.XiFPaper.S577QvPiRealizationFromS556Actual

end
