import tmp.sheaf.xif.paper.S550QvPhiPreFrobenioidActual
import tmp.sheaf.xif.paper.S438QVFamilyKSideCandidateActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

/-! # S564: candidate q_v/pi element of O^triangle from qVFamilyK.order

The endomorphism is constructed conditionally on a rational function whose
divisor is `qOrder`.  The model Input does not itself provide such a pi;
the exact missing datum is isolated below.
-/

namespace LeanFormal.IUT.XiFPaper.S564QvPiOtriangleCandidateActual

open CategoryTheory
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S432SmallModelActual
open LeanFormal.IUT.XiFPaper.S511PhiCvCandidateActual
open LeanFormal.IUT.XiFPaper.S522QvPhiRamificationModelActual
open LeanFormal.IUT.XiFPaper.S550QvPhiPreFrobenioidActual
open LeanFormal.IUT.XiFPaper.S438QVFamilyKSideCandidateActual
open Iut.SourceModelFrobenioid

universe u
variable {K : Type u} [Field K]
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable (R : RamificationIndexData (K := K))
variable (data : Input (qvPhi (K := K) R))

/-- The actual K-side q_v order used as the π divisor. -/
noncomputable def qvPiOrder (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) : ℕ := (qVFamilyK T b).order

theorem qvPiOrder_pos (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) : 0 < qvPiOrder T b :=
  (qVFamilyK T b).order_pos

/-- Conditional rational-function realization of the q_v divisor. -/
structure QvPiRealization where
  A : Object (qvPhi (K := K) R)
  rationalFunction : data.rationalFunctions.obj A.base
  divisor_eq :
    data.divisor A.base rationalFunction =
      Algebra.GrothendieckAddGroup.of (ULift.up (qvPiOrder T b))

/-- Conditional O^triangle element: base-identity linear endomorphism with
divisor `qOrder` and the supplied rational function. -/
noncomputable def qvPiEndomorphism
    (P : QvPiRealization (K := K) T b R data) :
    (qvPreFrobenioid (K := K) R data).LinearBaseIdentityEndomorphism P.A where
  hom :=
    { frobeniusDegree := 1
      base := 𝟙 P.A.base
      divisor := ULift.up (qvPiOrder T b)
      rationalFunction := P.rationalFunction
      balance := by
        change (1 : ℕ) • P.A.divisorClass +
            Algebra.GrothendieckAddGroup.of
              (M := ((qvPhi (K := K) R).obj P.A.base).carrier)
              (ULift.up (qvPiOrder T b)) =
          gpPullback (qvPhi (K := K) R) (𝟙 P.A.base) P.A.divisorClass +
            data.divisor P.A.base P.rationalFunction
        rw [one_nsmul, gpPullback_id]
        simp [P.divisor_eq]
        rfl }
  linear := rfl
  baseIdentity := rfl

theorem qvPiEndomorphism_divisor
    (P : QvPiRealization (K := K) T b R data) :
    (qvPiEndomorphism (K := K) T b R data P).hom.divisor =
      ULift.up (qvPiOrder T b) := rfl

theorem qvPiEndomorphism_rationalFunction
    (P : QvPiRealization (K := K) T b R data) :
    (qvPiEndomorphism (K := K) T b R data P).hom.rationalFunction =
      P.rationalFunction := rfl

/-- Exact required datum for the q_v π element. -/
def QvPiRealizationRequired : Prop := Nonempty (QvPiRealization (K := K) T b R data)

theorem qvPiRealizationRequired_iff :
    QvPiRealizationRequired (K := K) T b R data ↔
      ∃ (A : Object (qvPhi (K := K) R))
        (r : data.rationalFunctions.obj A.base),
        data.divisor A.base r =
          Algebra.GrothendieckAddGroup.of (ULift.up (qvPiOrder T b)) := by
  constructor
  · rintro ⟨P⟩
    exact ⟨P.A, P.rationalFunction, P.divisor_eq⟩
  · rintro ⟨A, r, hr⟩
    exact ⟨{ A := A, rationalFunction := r, divisor_eq := hr }⟩

end LeanFormal.IUT.XiFPaper.S564QvPiOtriangleCandidateActual

end
