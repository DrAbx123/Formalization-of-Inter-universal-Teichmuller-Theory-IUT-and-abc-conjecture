import tmp.sheaf.xif.paper.S571QvPhiUnitDecompositionActual
import tmp.sheaf.xif.paper.S601QvPhiQOrderFieldsFromPreimageActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

/-! # S603: exact divisor-divisibility/decomposition goal for O^triangle -/

namespace LeanFormal.IUT.XiFPaper.S603QvPhiDivisibilityGoalActual

open CategoryTheory
open Iut
open LeanFormal.IUT.XiFPaper.S432SmallModelActual
open LeanFormal.IUT.XiFPaper.S511PhiCvCandidateActual
open LeanFormal.IUT.XiFPaper.S522QvPhiRamificationModelActual
open LeanFormal.IUT.XiFPaper.S550QvPhiPreFrobenioidActual
open LeanFormal.IUT.XiFPaper.S561QvPhiMinimalPackageActual
open LeanFormal.IUT.XiFPaper.S566QvPhiQOrderFieldsActual
open LeanFormal.IUT.XiFPaper.S571QvPhiUnitDecompositionActual
open LeanFormal.IUT.XiFPaper.S575QvPhiPositivePreimageActual
open LeanFormal.IUT.XiFPaper.S601QvPhiQOrderFieldsFromPreimageActual
open Iut.SourceModelFrobenioid

universe u
variable {K : Type u} [Field K]
variable (P : S561MinimalPackage (K := K))
variable (A : Object (qvPhi (K := K) P.ramification))
variable {qOrder : ℕ}
variable (H : PositiveQvPhiPreimage (K := K) P A qOrder)

abbrev threeInput : Input (qvPhi (K := K) P.ramification) :=
  s566Input (K := K) P

abbrev threePi :
    PreFrobenioid.LinearBaseIdentityEndomorphism
      (P := qvPreFrobenioid (K := K) P.ramification (threeInput (K := K) P)) A :=
  qOrderEndomorphismOfPreimage (K := K) P A H

theorem threePi_divisor : (threePi (K := K) P A H).hom.divisor = H.divisor := rfl

/-- Exact goal for one O^triangle element: its divisor is an integer multiple
of the qOrder divisor. -/
def DivisorDivisibilityGoal
    (a : PreFrobenioid.LinearBaseIdentityEndomorphism
      (P := qvPreFrobenioid (K := K) P.ramification (threeInput (K := K) P)) A) : Prop :=
  ∃ n : ℕ, a.hom.divisor = n • H.divisor

/-- Exact required uniform statement: every O^triangle element has divisible
divisor. -/
def DivisorDivisibilityRequired : Prop :=
  ∀ a : PreFrobenioid.LinearBaseIdentityEndomorphism
    (P := qvPreFrobenioid (K := K) P.ramification (threeInput (K := K) P)) A,
    DivisorDivisibilityGoal (K := K) P A H a

/-- Explicit witness package for the divisibility goal.  This is the exact
datum not produced by S601: the integer n and the divisor equality. -/
structure DivisorDivisibilityWitness
    (a : PreFrobenioid.LinearBaseIdentityEndomorphism
      (P := qvPreFrobenioid (K := K) P.ramification (threeInput (K := K) P)) A) where
  exponent : ℕ
  divisor_eq : a.hom.divisor = exponent • H.divisor

theorem divisorDivisibilityGoal_of_witness
    {a : PreFrobenioid.LinearBaseIdentityEndomorphism
      (P := qvPreFrobenioid (K := K) P.ramification (threeInput (K := K) P)) A}
    (W : DivisorDivisibilityWitness (K := K) P A H a) :
    DivisorDivisibilityGoal (K := K) P A H a :=
  ⟨W.exponent, W.divisor_eq⟩

/-- Exact decomposition form with a genuine unit part. -/
structure UnitTimesPiData
    (a : PreFrobenioid.LinearBaseIdentityEndomorphism
      (P := qvPreFrobenioid (K := K) P.ramification (threeInput (K := K) P)) A) where
  unit_part : Units (PreFrobenioid.LinearBaseIdentityEndomorphism
    (P := qvPreFrobenioid (K := K) P.ramification (threeInput (K := K) P)) A)
  exponent : ℕ
  decomposition :
    a = (unit_part : PreFrobenioid.LinearBaseIdentityEndomorphism
      (P := qvPreFrobenioid (K := K) P.ramification (threeInput (K := K) P)) A) *
      threePi (K := K) P A H ^ exponent
  unique_exponent :
    ∀ (u : Units (PreFrobenioid.LinearBaseIdentityEndomorphism
      (P := qvPreFrobenioid (K := K) P.ramification (threeInput (K := K) P)) A)) (m : ℕ),
      a = (u : PreFrobenioid.LinearBaseIdentityEndomorphism
        (P := qvPreFrobenioid (K := K) P.ramification (threeInput (K := K) P)) A) *
        threePi (K := K) P A H ^ m → m = exponent

theorem unitTimesPiData_unit (a) (D : UnitTimesPiData (K := K) P A H a) :
    IsUnit ((D.unit_part : PreFrobenioid.LinearBaseIdentityEndomorphism
      (P := qvPreFrobenioid (K := K) P.ramification (threeInput (K := K) P)) A)) := by
  exact D.unit_part.isUnit

end LeanFormal.IUT.XiFPaper.S603QvPhiDivisibilityGoalActual

end
