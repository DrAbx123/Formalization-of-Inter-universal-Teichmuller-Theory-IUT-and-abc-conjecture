import tmp.sheaf.xif.paper.S522QvPhiRamificationModelActual
import Iut.Foundations.SourceModelFrobenioid
import Iut.Foundations.SourceModelRationalMonoidTransport

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

/-! # S550: actual PreFrobenioid and rational transport on qvPhiRamificationModel

An explicit `Input` parameter supplies the rational-function monoid and
divisor naturality.  From it the model pre-Frobenioid and its RationalMonoidTransport
are actual.  The tau/CharacteristicSplitting part remains the exact missing data.
-/

namespace LeanFormal.IUT.XiFPaper.S550QvPhiPreFrobenioidActual

open CategoryTheory
open Iut
open LeanFormal.IUT.XiFPaper.S432SmallModelActual
open LeanFormal.IUT.XiFPaper.S511PhiCvCandidateActual
open LeanFormal.IUT.XiFPaper.S522QvPhiRamificationModelActual
open Iut.SourceModelFrobenioid

universe u
variable {K : Type u} [Field K]
variable (R : RamificationIndexData (K := K))

abbrev qvPhi := qvPhiRamificationModel (K := K) R
abbrev qvIsFSM : ∀ {X Y : Example32SmallBase K}, (X ⟶ Y) → Prop := fun {X Y} f => IsIso f

-- Explicit Input parameter: rationalFunctions + divisor + naturality.
variable (data : Input (qvPhi  R))

/-- Actual model PreFrobenioid from the explicit Input. -/
noncomputable def qvPreFrobenioid :
    PreFrobenioid (SourceModelFrobenioid.Carrier (qvPhi  R) data)
      (Example32SmallBase K ) (qvIsFSM ) :=
  SourceModelFrobenioid.Carrier.preFrobenioid
    (Phi := qvPhi  R) (data := data)

/-- Actual RationalMonoidTransport. -/
noncomputable def qvRationalMonoidTransport :
    (qvPreFrobenioid  R data).RationalMonoidTransport :=
  SourceModelFrobenioid.Carrier.rationalMonoidTransport
    (Phi := qvPhi  R) (data := data)

/-- Tau data for CharacteristicSplitting. -/
structure QvPhiTauData where
  tau : ∀ X : (qvPreFrobenioid  R data).IsotropicLinearObject,
    Submonoid ((qvPreFrobenioid  R data).LinearBaseIdentityEndomorphism X.obj)
  pullback_mem :
    ∀ {X Y : (qvPreFrobenioid  R data).IsotropicLinearObject} (f : X ⟶ Y)
      (value : (qvPreFrobenioid  R data).LinearBaseIdentityEndomorphism Y.obj),
      value ∈ tau Y → (qvRationalMonoidTransport  R data).pullback f value ∈ tau X
  units_commute :
    ∀ (X : (qvPreFrobenioid  R data).IsotropicLinearObject)
      (unit : Units ((qvPreFrobenioid  R data).LinearBaseIdentityEndomorphism X.obj))
      (characteristic : tau X),
      Commute (unit : (qvPreFrobenioid  R data).LinearBaseIdentityEndomorphism X.obj)
        characteristic.1
  multiplication_bijective :
    ∀ X : (qvPreFrobenioid  R data).IsotropicLinearObject,
      Function.Bijective
        (fun pair : Units ((qvPreFrobenioid  R data).LinearBaseIdentityEndomorphism X.obj) × tau X =>
          (pair.1 : (qvPreFrobenioid  R data).LinearBaseIdentityEndomorphism X.obj) * pair.2.1)
  isotropicHull_mem_range :
    ∀ (A : SourceModelFrobenioid.Carrier (qvPhi  R) data)
      (hull : (qvPreFrobenioid  R data).IsotropicHull A)
      (characteristic : tau { obj := hull.hull, isotropic := hull.isotropic }),
      characteristic.1 ∈ Set.range
        ((qvRationalMonoidTransport  R data).hullInclusion A hull)

noncomputable def characteristicSplittingOfTauData
    (D : QvPhiTauData  R data) :
    (qvPreFrobenioid  R data).CharacteristicSplitting
      (qvRationalMonoidTransport  R data) where
  tau := D.tau
  pullback_mem := D.pullback_mem
  units_commute := D.units_commute
  multiplication_bijective := D.multiplication_bijective
  isotropicHull_mem_range := D.isotropicHull_mem_range

def QvPhiTauRequired : Prop := Nonempty (QvPhiTauData  R data)

theorem qvPhiTauRequired_iff :
    QvPhiTauRequired  R data ↔
      Nonempty ((qvPreFrobenioid  R data).CharacteristicSplitting
        (qvRationalMonoidTransport  R data)) := by
  constructor
  · rintro ⟨D⟩
    exact ⟨characteristicSplittingOfTauData  R data D⟩
  · rintro ⟨S⟩
    exact ⟨{ tau := S.tau
             pullback_mem := S.pullback_mem
             units_commute := S.units_commute
             multiplication_bijective := S.multiplication_bijective
             isotropicHull_mem_range := S.isotropicHull_mem_range }⟩

end LeanFormal.IUT.XiFPaper.S550QvPhiPreFrobenioidActual

end
