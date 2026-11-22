import tmp.sheaf.xif.paper.S568QvPhiQOrderTauActual
import tmp.sheaf.xif.paper.S601QvPhiQOrderFieldsFromPreimageActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 6000000
set_option synthInstance.maxHeartbeats 800000

namespace LeanFormal.IUT.XiFPaper.S604QvPhiQOrderTauInputActual
open CategoryTheory
open Iut
open LeanFormal.IUT.XiFPaper.S432SmallModelActual
open LeanFormal.IUT.XiFPaper.S511PhiCvCandidateActual
open LeanFormal.IUT.XiFPaper.S522QvPhiRamificationModelActual
open LeanFormal.IUT.XiFPaper.S550QvPhiPreFrobenioidActual
open LeanFormal.IUT.XiFPaper.S555QvPhiTauConstructionGapActual
open LeanFormal.IUT.XiFPaper.S563QvOrderElementConstructionActual
open LeanFormal.IUT.XiFPaper.S568QvPhiQOrderTauActual
open LeanFormal.IUT.XiFPaper.S561QvPhiMinimalPackageActual
open LeanFormal.IUT.XiFPaper.S566QvPhiQOrderFieldsActual
open LeanFormal.IUT.XiFPaper.S575QvPhiPositivePreimageActual
open LeanFormal.IUT.XiFPaper.S601QvPhiQOrderFieldsFromPreimageActual
open Iut.SourceModelFrobenioid

universe u
variable {K : Type u} [Field K]
variable (P : S561MinimalPackage (K := K))

noncomputable def fieldsOfPreimageFamily
    (qOrder : ℕ)
    (H : ∀ X : (qvPreFrobenioid (K := K) P.ramification (s566Input P)).IsotropicLinearObject,
      PositiveQvPhiPreimage (K := K) P X.obj qOrder) :
    ∀ X : (qvPreFrobenioid (K := K) P.ramification (s566Input P)).IsotropicLinearObject,
      QvPhiQOrderFields (K := K) P.ramification (s566Input P) X.obj :=
  fun X => qvPhiQOrderFieldsOfPreimage (K := K) P X.obj (H X)

noncomputable def qvPhiQOrderTauInputOfPreimageFamily
    (qOrder : ℕ)
    (H : ∀ X : (qvPreFrobenioid (K := K) P.ramification (s566Input P)).IsotropicLinearObject,
      PositiveQvPhiPreimage (K := K) P X.obj qOrder)
    (pullback_mem : ∀ {X Y : (qvPreFrobenioid (K := K) P.ramification (s566Input P)).IsotropicLinearObject}
      (f : X ⟶ Y)
      (value : (qvPreFrobenioid (K := K) P.ramification (s566Input P)).LinearBaseIdentityEndomorphism Y.obj),
      value ∈ tauOfQOrderFields (K := K) P.ramification (s566Input P) Y.obj (fieldsOfPreimageFamily (K := K) P qOrder H Y) →
        (qvRationalMonoidTransport (K := K) P.ramification (s566Input P)).pullback f value ∈
          tauOfQOrderFields (K := K) P.ramification (s566Input P) X.obj (fieldsOfPreimageFamily (K := K) P qOrder H X))
    (units_commute : ∀ (X : (qvPreFrobenioid (K := K) P.ramification (s566Input P)).IsotropicLinearObject)
      (unit : Units ((qvPreFrobenioid (K := K) P.ramification (s566Input P)).LinearBaseIdentityEndomorphism X.obj))
      (characteristic : tauOfQOrderFields (K := K) P.ramification (s566Input P) X.obj (fieldsOfPreimageFamily (K := K) P qOrder H X)),
      Commute (unit : (qvPreFrobenioid (K := K) P.ramification (s566Input P)).LinearBaseIdentityEndomorphism X.obj)
        characteristic.1)
    (multiplication_bijective : ∀ X : (qvPreFrobenioid (K := K) P.ramification (s566Input P)).IsotropicLinearObject,
      Function.Bijective
        (fun pair : Units ((qvPreFrobenioid (K := K) P.ramification (s566Input P)).LinearBaseIdentityEndomorphism X.obj) ×
          tauOfQOrderFields (K := K) P.ramification (s566Input P) X.obj (fieldsOfPreimageFamily (K := K) P qOrder H X) =>
          (pair.1 : (qvPreFrobenioid (K := K) P.ramification (s566Input P)).LinearBaseIdentityEndomorphism X.obj) * pair.2.1))
    (isotropicHull_mem_range : ∀ (A : Carrier (qvPhi (K := K) P.ramification) (s566Input P))
      (hull : (qvPreFrobenioid (K := K) P.ramification (s566Input P)).IsotropicHull A)
      (characteristic : tauOfQOrderFields (K := K) P.ramification (s566Input P) hull.hull (fieldsOfPreimageFamily (K := K) P qOrder H { obj := hull.hull, isotropic := hull.isotropic })),
      characteristic.1 ∈ Set.range
        ((qvRationalMonoidTransport (K := K) P.ramification (s566Input P)).hullInclusion A hull)) :
    QvPhiQOrderTauInput (K := K) P.ramification (s566Input P) where
  fields := fieldsOfPreimageFamily (K := K) P qOrder H
  pullback_mem := pullback_mem
  units_commute := units_commute
  multiplication_bijective := multiplication_bijective
  isotropicHull_mem_range := isotropicHull_mem_range

noncomputable def tauDataOfPreimageFamily
    (PI : QvPhiQOrderTauInput (K := K) P.ramification (s566Input P)) :
    QvPhiTauData (K := K) P.ramification (s566Input P) :=
  tauDataOfQOrderInput (K := K) P.ramification (s566Input P) PI

noncomputable def characteristicSplittingOfPreimageFamily
    (PI : QvPhiQOrderTauInput (K := K) P.ramification (s566Input P)) :
    (qvPreFrobenioid (K := K) P.ramification (s566Input P)).CharacteristicSplitting
      (qvRationalMonoidTransport (K := K) P.ramification (s566Input P)) :=
  characteristicSplittingOfQOrderInput (K := K) P.ramification (s566Input P) PI

end LeanFormal.IUT.XiFPaper.S604QvPhiQOrderTauInputActual
end