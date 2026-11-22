import tmp.sheaf.xif.paper.S600PositiveFieldsFromS593Actual
import Iut.Foundations.Frobenioid

/-! # S615: units_commute for CharacteristicSplitting from S600 tau

S600 gives the actual positive tau.  The remaining CharacteristicSplitting
field units_commute is centrality of every unit of the endomorphism monoid;
it is recorded as an exact hypothesis, not assumed. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 6000000

namespace LeanFormal.IUT.XiFPaper.S615UnitsCommuteActual

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
open LeanFormal.IUT.XiFPaper.S556QvPhiInputActual
open LeanFormal.IUT.XiFPaper.S561QvPhiMinimalPackageActual
open LeanFormal.IUT.XiFPaper.S563QvOrderElementConstructionActual
open LeanFormal.IUT.XiFPaper.S566QvPhiQOrderFieldsActual
open LeanFormal.IUT.XiFPaper.S575QvPhiPositivePreimageActual
open LeanFormal.IUT.XiFPaper.S576PositiveQvPhiQOrderFieldsActual
open LeanFormal.IUT.XiFPaper.S593PositivePreimageQvOrderActual
open LeanFormal.IUT.XiFPaper.S600PositiveFieldsFromS593Actual
open LeanFormal.IUT.XiFPaper.S438QVFamilyKSideCandidateActual
open Iut.SourceModelFrobenioid

universe u
variable {K : Type u} [Field K]
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable (b : Bad (nativePlaceSelection T))
variable (P : S561MinimalPackage (K := K))

/-- Actual tau from S600, extended over isotropic linear objects. -/
noncomputable def s615Tau (X : (qvPreFrobenioid (K := K) P.ramification
    (s566Input (K := K) P)).IsotropicLinearObject) :
    Submonoid (PreFrobenioid.LinearBaseIdentityEndomorphism
      (P := qvPreFrobenioid (K := K) P.ramification
        (s566Input (K := K) P)) X.obj) :=
  s600Tau (K := K) T b P X.obj

/-- The exact units_commute statement for the S600 tau. -/
def S615UnitsCommuteStatement : Prop :=
  ∀ (X : (qvPreFrobenioid (K := K) P.ramification
      (s566Input (K := K) P)).IsotropicLinearObject)
    (unit : Units (PreFrobenioid.LinearBaseIdentityEndomorphism
      (P := qvPreFrobenioid (K := K) P.ramification
        (s566Input (K := K) P)) X.obj))
    (characteristic : s615Tau (K := K) T b P X),
    Commute (unit : PreFrobenioid.LinearBaseIdentityEndomorphism
      (P := qvPreFrobenioid (K := K) P.ramification
        (s566Input (K := K) P)) X.obj)
      characteristic.1

/-- Sufficient centrality condition: if all endomorphisms commute, then the
units_commute field holds immediately. -/
theorem s615UnitsCommute_of_commutative
    (h : ∀ (X : (qvPreFrobenioid (K := K) P.ramification
        (s566Input (K := K) P)).IsotropicLinearObject)
      (a b : PreFrobenioid.LinearBaseIdentityEndomorphism
        (P := qvPreFrobenioid (K := K) P.ramification
          (s566Input (K := K) P)) X.obj),
      Commute a b) :
    S615UnitsCommuteStatement (K := K) T b P := by
  intro X unit characteristic
  exact h X unit characteristic.1

/-- Exact missing units_commute datum. -/
def S615UnitsCommuteRequired : Prop :=
  S615UnitsCommuteStatement (K := K) T b P

/-- Conditional CharacteristicSplitting data with S600 tau and explicit
units_commute. -/
structure S615SplittingData where
  units_commute : S615UnitsCommuteStatement (K := K) T b P
  pullback_mem : Prop
  multiplication_bijective : Prop
  isotropicHull_mem_range : Prop

end LeanFormal.IUT.XiFPaper.S615UnitsCommuteActual

end
