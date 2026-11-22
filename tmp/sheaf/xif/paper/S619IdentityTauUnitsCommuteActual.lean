import tmp.sheaf.xif.paper.S615UnitsCommuteActual

/-! # S619: central/identity tau with actual units_commute

The S600 qOrder endomorphism is not a unit and centrality is not automatic.
Taking pi = 1 gives tau = powers 1 = {1}; every monoid unit commutes with 1,
so units_commute is proved.  The non-central qOrder commutator is recorded as
an exact separate requirement. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 6000000

namespace LeanFormal.IUT.XiFPaper.S619IdentityTauUnitsCommuteActual

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
open LeanFormal.IUT.XiFPaper.S615UnitsCommuteActual
open Iut.SourceModelFrobenioid

universe u
variable {K : Type u} [Field K]
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable (b : Bad (nativePlaceSelection T))
variable (P : S561MinimalPackage (K := K))

/-- Identity-generated tau: powers of 1. -/
noncomputable def s619IdentityTau
    (X : (qvPreFrobenioid (K := K) P.ramification
      (s566Input (K := K) P)).IsotropicLinearObject) :
    Submonoid (PreFrobenioid.LinearBaseIdentityEndomorphism
      (P := qvPreFrobenioid (K := K) P.ramification
        (s566Input (K := K) P)) X.obj) :=
  Submonoid.powers (1 : PreFrobenioid.LinearBaseIdentityEndomorphism
    (P := qvPreFrobenioid (K := K) P.ramification
      (s566Input (K := K) P)) X.obj)

/-- Every unit commutes with every element of the identity tau. -/
theorem s619IdentityTau_units_commute
    (X : (qvPreFrobenioid (K := K) P.ramification
      (s566Input (K := K) P)).IsotropicLinearObject)
    (unit : Units (PreFrobenioid.LinearBaseIdentityEndomorphism
      (P := qvPreFrobenioid (K := K) P.ramification
        (s566Input (K := K) P)) X.obj))
    (characteristic : s619IdentityTau (K := K) T b P X) :
    Commute (unit : PreFrobenioid.LinearBaseIdentityEndomorphism
      (P := qvPreFrobenioid (K := K) P.ramification
        (s566Input (K := K) P)) X.obj)
      characteristic.1 := by
  obtain ⟨n, hn⟩ :=
    (Submonoid.mem_powers_iff _ _).mp characteristic.2
  rw [← hn]
  simp

/-- Actual units_commute for the identity tau. -/
theorem s619IdentityTau_units_commute_statement :
    ∀ (X : (qvPreFrobenioid (K := K) P.ramification
        (s566Input (K := K) P)).IsotropicLinearObject)
      (unit : Units (PreFrobenioid.LinearBaseIdentityEndomorphism
        (P := qvPreFrobenioid (K := K) P.ramification
          (s566Input (K := K) P)) X.obj))
      (characteristic : s619IdentityTau (K := K) T b P X),
      Commute (unit : PreFrobenioid.LinearBaseIdentityEndomorphism
        (P := qvPreFrobenioid (K := K) P.ramification
          (s566Input (K := K) P)) X.obj)
        characteristic.1 :=
  s619IdentityTau_units_commute (K := K) T b P

/-- Exact non-central qOrder commutator datum (not asserted). -/
def S619QOrderCommuteRequired
    (X : (qvPreFrobenioid (K := K) P.ramification
      (s566Input (K := K) P)).IsotropicLinearObject) : Prop :=
  ∀ (unit : Units (PreFrobenioid.LinearBaseIdentityEndomorphism
      (P := qvPreFrobenioid (K := K) P.ramification
        (s566Input (K := K) P)) X.obj)),
    Commute (unit : PreFrobenioid.LinearBaseIdentityEndomorphism
      (P := qvPreFrobenioid (K := K) P.ramification
        (s566Input (K := K) P)) X.obj)
      (qOrderEndomorphismOfFields (K := K) P.ramification
        (s566Input (K := K) P) X.obj
        (s600QvPhiQOrderFields (K := K) T b P X.obj))

end LeanFormal.IUT.XiFPaper.S619IdentityTauUnitsCommuteActual

end
