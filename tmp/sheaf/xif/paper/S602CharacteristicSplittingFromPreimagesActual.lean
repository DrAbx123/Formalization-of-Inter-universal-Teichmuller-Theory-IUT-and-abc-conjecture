import tmp.sheaf.xif.paper.S601QvPhiQOrderFieldsFromPreimageActual
import tmp.sheaf.xif.paper.S568QvPhiQOrderTauActual
import tmp.sheaf.xif.paper.S580PositivePreimageConstructionActual

-- S602: actual per-object QvPhiQOrderFields from S601 preimages; the four
-- characteristic-splitting laws are explicit parameters.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S602CharacteristicSplittingFromPreimagesActual

open CategoryTheory
open Iut
open LeanFormal.IUT.XiFPaper.S432SmallModelActual
open LeanFormal.IUT.XiFPaper.S511PhiCvCandidateActual
open LeanFormal.IUT.XiFPaper.S522QvPhiRamificationModelActual
open LeanFormal.IUT.XiFPaper.S550QvPhiPreFrobenioidActual
open LeanFormal.IUT.XiFPaper.S555QvPhiTauConstructionGapActual
open LeanFormal.IUT.XiFPaper.S561QvPhiMinimalPackageActual
open LeanFormal.IUT.XiFPaper.S563QvOrderElementConstructionActual
open LeanFormal.IUT.XiFPaper.S566QvPhiQOrderFieldsActual
open LeanFormal.IUT.XiFPaper.S575QvPhiPositivePreimageActual
open LeanFormal.IUT.XiFPaper.S580PositivePreimageConstructionActual
open LeanFormal.IUT.XiFPaper.S601QvPhiQOrderFieldsFromPreimageActual
open LeanFormal.IUT.XiFPaper.S568QvPhiQOrderTauActual
open Iut.SourceModelFrobenioid

universe u
variable {K : Type u} [Field K]
variable (P : S561MinimalPackage (K := K))

noncomputable def preimageFields (qOrder : ℕ) (hpos : 0 < qOrder)
    (X : (qvPreFrobenioid (K := K) P.ramification (s566Input P)).IsotropicLinearObject) :
    QvPhiQOrderFields (K := K) P.ramification (s566Input P) X.obj :=
  qvPhiQOrderFieldsOfPreimage (K := K) P X.obj
    (S580PositivePreimageConstructionActual.positiveQvPhiPreimage (K := K) P X.obj qOrder hpos)

noncomputable def qvPhiQOrderTauInputOfPreimages
    (qOrder : ℕ) (hpos : 0 < qOrder)
    (pullback_mem :
      ∀ {X Y : (qvPreFrobenioid (K := K) P.ramification (s566Input P)).IsotropicLinearObject}
        (f : X ⟶ Y)
        (value : (qvPreFrobenioid (K := K) P.ramification (s566Input P)).LinearBaseIdentityEndomorphism Y.obj),
        value ∈ tauOfQOrderFields (K := K) P.ramification (s566Input P) Y.obj (preimageFields (K := K) P qOrder hpos Y) →
          (qvRationalMonoidTransport (K := K) P.ramification (s566Input P)).pullback f value ∈
            tauOfQOrderFields (K := K) P.ramification (s566Input P) X.obj (preimageFields (K := K) P qOrder hpos X))
    (units_commute :
      ∀ (X : (qvPreFrobenioid (K := K) P.ramification (s566Input P)).IsotropicLinearObject)
        (unit : Units ((qvPreFrobenioid (K := K) P.ramification (s566Input P)).LinearBaseIdentityEndomorphism X.obj))
        (characteristic : tauOfQOrderFields (K := K) P.ramification (s566Input P) X.obj (preimageFields (K := K) P qOrder hpos X)),
        Commute (unit : (qvPreFrobenioid (K := K) P.ramification (s566Input P)).LinearBaseIdentityEndomorphism X.obj)
          characteristic.1)
    (multiplication_bijective :
      ∀ X : (qvPreFrobenioid (K := K) P.ramification (s566Input P)).IsotropicLinearObject,
        Function.Bijective
          (fun pair : Units ((qvPreFrobenioid (K := K) P.ramification (s566Input P)).LinearBaseIdentityEndomorphism X.obj) ×
            tauOfQOrderFields (K := K) P.ramification (s566Input P) X.obj (preimageFields (K := K) P qOrder hpos X) =>
            (pair.1 : (qvPreFrobenioid (K := K) P.ramification (s566Input P)).LinearBaseIdentityEndomorphism X.obj) * pair.2.1))
    (isotropicHull_mem_range :
      ∀ (A : Carrier (qvPhi (K := K) P.ramification) (s566Input P))
        (hull : (qvPreFrobenioid (K := K) P.ramification (s566Input P)).IsotropicHull A)
        (characteristic : tauOfQOrderFields (K := K) P.ramification (s566Input P) hull.hull
          (preimageFields (K := K) P qOrder hpos { obj := hull.hull, isotropic := hull.isotropic })),
        characteristic.1 ∈ Set.range
          ((qvRationalMonoidTransport (K := K) P.ramification (s566Input P)).hullInclusion A hull)) :
    QvPhiQOrderTauInput (K := K) P.ramification (s566Input P) where
  fields := preimageFields (K := K) P qOrder hpos
  pullback_mem := pullback_mem
  units_commute := units_commute
  multiplication_bijective := multiplication_bijective
  isotropicHull_mem_range := isotropicHull_mem_range

noncomputable def characteristicSplittingOfPreimages
    (qOrder : ℕ) (hpos : 0 < qOrder)
    (pullback_mem :
      ∀ {X Y : (qvPreFrobenioid (K := K) P.ramification (s566Input P)).IsotropicLinearObject}
        (f : X ⟶ Y)
        (value : (qvPreFrobenioid (K := K) P.ramification (s566Input P)).LinearBaseIdentityEndomorphism Y.obj),
        value ∈ tauOfQOrderFields (K := K) P.ramification (s566Input P) Y.obj (preimageFields (K := K) P qOrder hpos Y) →
          (qvRationalMonoidTransport (K := K) P.ramification (s566Input P)).pullback f value ∈
            tauOfQOrderFields (K := K) P.ramification (s566Input P) X.obj (preimageFields (K := K) P qOrder hpos X))
    (units_commute :
      ∀ (X : (qvPreFrobenioid (K := K) P.ramification (s566Input P)).IsotropicLinearObject)
        (unit : Units ((qvPreFrobenioid (K := K) P.ramification (s566Input P)).LinearBaseIdentityEndomorphism X.obj))
        (characteristic : tauOfQOrderFields (K := K) P.ramification (s566Input P) X.obj (preimageFields (K := K) P qOrder hpos X)),
        Commute (unit : (qvPreFrobenioid (K := K) P.ramification (s566Input P)).LinearBaseIdentityEndomorphism X.obj)
          characteristic.1)
    (multiplication_bijective :
      ∀ X : (qvPreFrobenioid (K := K) P.ramification (s566Input P)).IsotropicLinearObject,
        Function.Bijective
          (fun pair : Units ((qvPreFrobenioid (K := K) P.ramification (s566Input P)).LinearBaseIdentityEndomorphism X.obj) ×
            tauOfQOrderFields (K := K) P.ramification (s566Input P) X.obj (preimageFields (K := K) P qOrder hpos X) =>
            (pair.1 : (qvPreFrobenioid (K := K) P.ramification (s566Input P)).LinearBaseIdentityEndomorphism X.obj) * pair.2.1))
    (isotropicHull_mem_range :
      ∀ (A : Carrier (qvPhi (K := K) P.ramification) (s566Input P))
        (hull : (qvPreFrobenioid (K := K) P.ramification (s566Input P)).IsotropicHull A)
        (characteristic : tauOfQOrderFields (K := K) P.ramification (s566Input P) hull.hull
          (preimageFields (K := K) P qOrder hpos { obj := hull.hull, isotropic := hull.isotropic })),
        characteristic.1 ∈ Set.range
          ((qvRationalMonoidTransport (K := K) P.ramification (s566Input P)).hullInclusion A hull))
    :
    (qvPreFrobenioid (K := K) P.ramification (s566Input P)).CharacteristicSplitting
      (qvRationalMonoidTransport (K := K) P.ramification (s566Input P)) :=
  characteristicSplittingOfQOrderInput (K := K) P.ramification (s566Input P)
    (qvPhiQOrderTauInputOfPreimages (K := K) P qOrder hpos
      pullback_mem units_commute multiplication_bijective isotropicHull_mem_range)
#check preimageFields
#check qvPhiQOrderTauInputOfPreimages
#check characteristicSplittingOfPreimages

end LeanFormal.IUT.XiFPaper.S602CharacteristicSplittingFromPreimagesActual

end