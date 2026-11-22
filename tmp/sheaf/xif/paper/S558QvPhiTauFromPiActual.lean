import tmp.sheaf.xif.paper.S550QvPhiPreFrobenioidActual
import tmp.sheaf.xif.paper.S547PhiCvPackageActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S558QvPhiTauFromPiActual

open CategoryTheory
open Iut
open LeanFormal.IUT.XiFPaper.S432SmallModelActual
open LeanFormal.IUT.XiFPaper.S511PhiCvCandidateActual
open LeanFormal.IUT.XiFPaper.S522QvPhiRamificationModelActual
open LeanFormal.IUT.XiFPaper.S550QvPhiPreFrobenioidActual
open Iut.SourceModelFrobenioid

universe u
variable {K : Type u} [Field K]
variable (R : RamificationIndexData (K := K))
variable (data : Input (qvPhiRamificationModel (K := K) R))

/-- A concrete π in each O^triangle monoid, its pow submonoid, and the laws
needed for tau.  This is the exact missing input: the current qvPhi package
carries qOrder/submonoid on the divisor monoid, not a carrier endomorphism. -/
structure QvPhiPiTauInput where
  pi : ∀ X : (qvPreFrobenioid (K := K) R data).IsotropicLinearObject,
    (qvPreFrobenioid (K := K) R data).LinearBaseIdentityEndomorphism X.obj
  tau : ∀ X : (qvPreFrobenioid (K := K) R data).IsotropicLinearObject,
    Submonoid ((qvPreFrobenioid (K := K) R data).LinearBaseIdentityEndomorphism X.obj)
  tau_eq : ∀ X, tau X = Submonoid.closure ({pi X} : Set _)
  pullback_mem :
    ∀ {X Y : (qvPreFrobenioid (K := K) R data).IsotropicLinearObject} (f : X ⟶ Y)
      (value : (qvPreFrobenioid (K := K) R data).LinearBaseIdentityEndomorphism Y.obj),
      value ∈ tau Y →
        (qvRationalMonoidTransport (K := K) R data).pullback f value ∈ tau X
  units_commute :
    ∀ (X : (qvPreFrobenioid (K := K) R data).IsotropicLinearObject)
      (unit : Units ((qvPreFrobenioid (K := K) R data).LinearBaseIdentityEndomorphism X.obj))
      (characteristic : tau X),
      Commute (unit : (qvPreFrobenioid (K := K) R data).LinearBaseIdentityEndomorphism X.obj)
        characteristic.1
  multiplication_bijective :
    ∀ X : (qvPreFrobenioid (K := K) R data).IsotropicLinearObject,
      Function.Bijective
        (fun pair : Units ((qvPreFrobenioid (K := K) R data).LinearBaseIdentityEndomorphism X.obj) × tau X =>
          (pair.1 : (qvPreFrobenioid (K := K) R data).LinearBaseIdentityEndomorphism X.obj) * pair.2.1)
  isotropicHull_mem_range :
    ∀ (A : Carrier (qvPhiRamificationModel (K := K) R) data)
      (hull : (qvPreFrobenioid (K := K) R data).IsotropicHull A)
      (characteristic : tau { obj := hull.hull, isotropic := hull.isotropic }),
      characteristic.1 ∈ Set.range
        ((qvRationalMonoidTransport (K := K) R data).hullInclusion A hull)

noncomputable def tauDataOfPiInput
    (P : QvPhiPiTauInput (K := K) R data) : QvPhiTauData (K := K) R data where
  tau := P.tau
  pullback_mem := P.pullback_mem
  units_commute := P.units_commute
  multiplication_bijective := P.multiplication_bijective
  isotropicHull_mem_range := P.isotropicHull_mem_range

noncomputable def characteristicSplittingOfPiInput
    (P : QvPhiPiTauInput (K := K) R data) :
    (qvPreFrobenioid (K := K) R data).CharacteristicSplitting
      (qvRationalMonoidTransport (K := K) R data) :=
  characteristicSplittingOfTauData (K := K) R data (tauDataOfPiInput (K := K) R data P)

/-- Exact missing concrete π/decomposition/hull data. -/
def QvPhiPiTauInputRequired : Prop :=
  Nonempty (QvPhiPiTauInput (K := K) R data)

end LeanFormal.IUT.XiFPaper.S558QvPhiTauFromPiActual

end
