import tmp.sheaf.xif.paper.S597QvPhiQOrderFieldsActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S608QOrderDivisibilityLawsActual

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
open LeanFormal.IUT.XiFPaper.S561QvPhiMinimalPackageActual
open LeanFormal.IUT.XiFPaper.S563QvOrderElementConstructionActual
open LeanFormal.IUT.XiFPaper.S566QvPhiQOrderFieldsActual
open LeanFormal.IUT.XiFPaper.S597QvPhiQOrderFieldsActual
open Iut.SourceModelFrobenioid

universe u
variable {K : Type u} [Field K]
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable (P : S561MinimalPackage (K := K))
variable (A : Object (qvPhi (K := K) P.ramification))

abbrev qvPi := qOrderEndomorphism (K := K) T b P A
abbrev qvFields := qOrderFields (K := K) T b P A

theorem lbEnd_mul_divisor
    (x y : PreFrobenioid.LinearBaseIdentityEndomorphism
      (P := qvPreFrobenioid (K := K) P.ramification (s566Input (K := K) P)) A) :
    (x * y).hom.divisor = x.hom.divisor + y.hom.divisor := by
  change (x.hom ≫ y.hom).divisor = x.hom.divisor + y.hom.divisor
  have hx : x.hom.base = 𝟙 A.base := x.baseIdentity
  have hy : y.hom.frobeniusDegree = 1 := y.linear
  rw [Carrier.comp_divisor, hx, hy]
  change (qvPhi (K := K) P.ramification).pullback (𝟙 A.base) y.hom.divisor + 1 • x.hom.divisor =
    x.hom.divisor + y.hom.divisor
  rw [(qvPhi (K := K) P.ramification).pullback_id]
  simp
  abel

theorem qvPi_divisor :
    (qvPi (K := K) T b P A).hom.divisor = (qvFields (K := K) T b P A).divisor := rfl

theorem qvPi_pow_divisor (n : ℕ) :
    ((qvPi (K := K) T b P A) ^ n).hom.divisor =
      n • (qvFields (K := K) T b P A).divisor := by
  induction n with
  | zero =>
      rw [pow_zero]
      rfl
  | succ n ih =>
      rw [pow_succ]
      rw [lbEnd_mul_divisor]
      rw [ih, qvPi_divisor]
      rw [succ_nsmul]
      rfl

def DivisorDivisibilityGoal
    (a : PreFrobenioid.LinearBaseIdentityEndomorphism
      (P := qvPreFrobenioid (K := K) P.ramification (s566Input (K := K) P)) A) : Prop :=
  ∃ n : ℕ, a.hom.divisor = n • (qvFields (K := K) T b P A).divisor

def DivisorDivisibilityRequired : Prop :=
  ∀ a : PreFrobenioid.LinearBaseIdentityEndomorphism
    (P := qvPreFrobenioid (K := K) P.ramification (s566Input (K := K) P)) A,
    DivisorDivisibilityGoal (K := K) T b P A a

theorem tau_power_divisibility (n : ℕ) :
    DivisorDivisibilityGoal (K := K) T b P A ((qvPi (K := K) T b P A) ^ n) :=
  ⟨n, qvPi_pow_divisor (K := K) T b P A n⟩

def UnitsCommuteWithPiGoal : Prop :=
  ∀ (u : Units (PreFrobenioid.LinearBaseIdentityEndomorphism
      (P := qvPreFrobenioid (K := K) P.ramification (s566Input (K := K) P)) A))
    (n : ℕ),
    Commute (u : PreFrobenioid.LinearBaseIdentityEndomorphism
      (P := qvPreFrobenioid (K := K) P.ramification (s566Input (K := K) P)) A)
      ((qvPi (K := K) T b P A) ^ n)

def MultiplicationBijectiveGoal : Prop :=
  Function.Bijective
    (fun pair : Units (PreFrobenioid.LinearBaseIdentityEndomorphism
      (P := qvPreFrobenioid (K := K) P.ramification (s566Input (K := K) P)) A) ×
      Submonoid.powers (qvPi (K := K) T b P A) =>
      (pair.1 : PreFrobenioid.LinearBaseIdentityEndomorphism
        (P := qvPreFrobenioid (K := K) P.ramification (s566Input (K := K) P)) A) *
        pair.2.1)

def IsotropicHullGoal : Prop :=
  ∀ (X : Carrier (qvPhi (K := K) P.ramification) (s566Input (K := K) P))
    (hull : (qvPreFrobenioid (K := K) P.ramification (s566Input (K := K) P)).IsotropicHull X)
    (characteristic : Submonoid.powers
      (qOrderEndomorphism (K := K) T b P hull.hull)),
    characteristic.1 ∈ Set.range
      ((qvRationalMonoidTransport (K := K) P.ramification (s566Input (K := K) P)).hullInclusion X hull)

end LeanFormal.IUT.XiFPaper.S608QOrderDivisibilityLawsActual

end
