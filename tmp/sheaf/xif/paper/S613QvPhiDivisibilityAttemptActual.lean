import tmp.sheaf.xif.paper.S603QvPhiDivisibilityGoalActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S613QvPhiDivisibilityAttemptActual

open CategoryTheory
open Iut
open LeanFormal.IUT.XiFPaper.S432SmallModelActual
open LeanFormal.IUT.XiFPaper.S511PhiCvCandidateActual
open LeanFormal.IUT.XiFPaper.S522QvPhiRamificationModelActual
open LeanFormal.IUT.XiFPaper.S550QvPhiPreFrobenioidActual
open LeanFormal.IUT.XiFPaper.S561QvPhiMinimalPackageActual
open LeanFormal.IUT.XiFPaper.S566QvPhiQOrderFieldsActual
open LeanFormal.IUT.XiFPaper.S575QvPhiPositivePreimageActual
open LeanFormal.IUT.XiFPaper.S601QvPhiQOrderFieldsFromPreimageActual
open LeanFormal.IUT.XiFPaper.S603QvPhiDivisibilityGoalActual
open Iut.SourceModelFrobenioid

universe u
variable {K : Type u} [Field K]
variable (P : S561MinimalPackage (K := K))
variable (A : Object (qvPhi (K := K) P.ramification))
variable {qOrder : ℕ}
variable (H : PositiveQvPhiPreimage (K := K) P A qOrder)

abbrev divMon : Type _ :=
  PreFrobenioid.LinearBaseIdentityEndomorphism
    (P := qvPreFrobenioid (K := K) P.ramification (s566Input (K := K) P)) A

theorem identity_divisorDivisibility :
    DivisorDivisibilityGoal (K := K) P A H (1 : divMon P A) := by
  refine ⟨0, ?_⟩
  rw [zero_nsmul]
  rfl

/-- A true counterexample would be an O^triangle element whose divisor is not
an integer multiple of H.divisor.  The current tree does not construct one;
this is the exact missing counterexample datum. -/
structure DivisorDivisibilityCounterexample where
  a : divMon P A
  not_divisible : ¬ DivisorDivisibilityGoal (K := K) P A H a

def DivisorDivisibilityCounterexampleRequired : Prop :=
  Nonempty (DivisorDivisibilityCounterexample (K := K) P A H)

/-- The general divisibility statement from S603 remains unproved. -/
def QvPhiGeneralDivisibilityOpen : Prop :=
  DivisorDivisibilityRequired (K := K) P A H

end LeanFormal.IUT.XiFPaper.S613QvPhiDivisibilityAttemptActual

end
