import tmp.sheaf.xif.paper.S575QvPhiPositivePreimageActual
import tmp.sheaf.xif.paper.S568QvPhiQOrderTauActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 800000

namespace LeanFormal.IUT.XiFPaper.S599QvPhiTauFieldsActual

open CategoryTheory
open Iut
open LeanFormal.IUT.XiFPaper.S432SmallModelActual
open LeanFormal.IUT.XiFPaper.S511PhiCvCandidateActual
open LeanFormal.IUT.XiFPaper.S522QvPhiRamificationModelActual
open LeanFormal.IUT.XiFPaper.S550QvPhiPreFrobenioidActual
open LeanFormal.IUT.XiFPaper.S563QvOrderElementConstructionActual
open LeanFormal.IUT.XiFPaper.S556QvPhiInputActual
open LeanFormal.IUT.XiFPaper.S561QvPhiMinimalPackageActual
open LeanFormal.IUT.XiFPaper.S566QvPhiQOrderFieldsActual
open LeanFormal.IUT.XiFPaper.S568QvPhiQOrderTauActual
open LeanFormal.IUT.XiFPaper.S575QvPhiPositivePreimageActual
open Iut.SourceModelFrobenioid

universe u
variable {K : Type u} [Field K]
variable (P : S561MinimalPackage (K := K))
variable (qOrder : ℕ) (hq : 0 < qOrder)

/-- Actual qOrder fields from the S575 positive preimage, for every isotropic
linear object. -/
noncomputable def s599QOrderFields
    (X : (qvPreFrobenioid (K := K) P.ramification (s566Input P)).IsotropicLinearObject) :
    QvPhiQOrderFields (K := K) P.ramification (s566Input P) X.obj where
  divisor := (positiveQvPhiPreimage (K := K) P X.obj qOrder hq).divisor
  rationalFunction := (positiveQvPhiPreimage (K := K) P X.obj qOrder hq).rationalFunction
  divisor_eq := (positiveQvPhiPreimage (K := K) P X.obj qOrder hq).divisor_eq

/-- Compatibility fields for the S568 QvPhiQOrderTauInput; these are the
remaining inputs, not fabricated. -/
structure S599TauCompatibility where
  pullback_mem :
    ∀ {X Y : (qvPreFrobenioid (K := K) P.ramification (s566Input P)).IsotropicLinearObject}
      (f : X ⟶ Y)
      (value : (qvPreFrobenioid (K := K) P.ramification (s566Input P)).LinearBaseIdentityEndomorphism Y.obj),
      value ∈ tauOfQOrderFields (K := K) P.ramification (s566Input P) Y.obj
        (s599QOrderFields (K := K) P qOrder hq Y) →
        (qvRationalMonoidTransport (K := K) P.ramification (s566Input P)).pullback f value ∈
          tauOfQOrderFields (K := K) P.ramification (s566Input P) X.obj
            (s599QOrderFields (K := K) P qOrder hq X)
  units_commute :
    ∀ (X : (qvPreFrobenioid (K := K) P.ramification (s566Input P)).IsotropicLinearObject)
      (unit : Units ((qvPreFrobenioid (K := K) P.ramification (s566Input P)).LinearBaseIdentityEndomorphism X.obj))
      (characteristic : tauOfQOrderFields (K := K) P.ramification (s566Input P) X.obj
        (s599QOrderFields (K := K) P qOrder hq X)),
      Commute (unit : (qvPreFrobenioid (K := K) P.ramification (s566Input P)).LinearBaseIdentityEndomorphism X.obj)
        characteristic.1
  multiplication_bijective :
    ∀ X : (qvPreFrobenioid (K := K) P.ramification (s566Input P)).IsotropicLinearObject,
      Function.Bijective
        (fun pair : Units ((qvPreFrobenioid (K := K) P.ramification (s566Input P)).LinearBaseIdentityEndomorphism X.obj) ×
          tauOfQOrderFields (K := K) P.ramification (s566Input P) X.obj
            (s599QOrderFields (K := K) P qOrder hq X) =>
          (pair.1 : (qvPreFrobenioid (K := K) P.ramification (s566Input P)).LinearBaseIdentityEndomorphism X.obj) * pair.2.1)
  isotropicHull_mem_range :
    ∀ (A : Carrier (qvPhi (K := K) P.ramification) (s566Input P))
      (hull : (qvPreFrobenioid (K := K) P.ramification (s566Input P)).IsotropicHull A)
      (characteristic : tauOfQOrderFields (K := K) P.ramification (s566Input P) hull.hull
        (s599QOrderFields (K := K) P qOrder hq { obj := hull.hull, isotropic := hull.isotropic })),
      characteristic.1 ∈ Set.range
        ((qvRationalMonoidTransport (K := K) P.ramification (s566Input P)).hullInclusion A hull)

/-- Actual S568 input with fields from the S575 preimage and compatibility as
explicit data. -/
noncomputable def s599QvPhiQOrderTauInput
    (C : S599TauCompatibility (K := K) P qOrder hq) :
    QvPhiQOrderTauInput (K := K) P.ramification (s566Input P) where
  fields := s599QOrderFields (K := K) P qOrder hq
  pullback_mem := C.pullback_mem
  units_commute := C.units_commute
  multiplication_bijective := C.multiplication_bijective
  isotropicHull_mem_range := C.isotropicHull_mem_range

/-- Actual tau data. -/
noncomputable def s599TauData
    (C : S599TauCompatibility (K := K) P qOrder hq) :
    QvPhiTauData (K := K) P.ramification (s566Input P) :=
  tauDataOfQOrderInput (K := K) P.ramification (s566Input P)
    (s599QvPhiQOrderTauInput (K := K) P qOrder hq C)

/-- Actual characteristic splitting. -/
noncomputable def s599CharacteristicSplitting
    (C : S599TauCompatibility (K := K) P qOrder hq) :
    (qvPreFrobenioid (K := K) P.ramification (s566Input P)).CharacteristicSplitting
      (qvRationalMonoidTransport (K := K) P.ramification (s566Input P)) :=
  characteristicSplittingOfQOrderInput (K := K) P.ramification (s566Input P)
    (s599QvPhiQOrderTauInput (K := K) P qOrder hq C)


end LeanFormal.IUT.XiFPaper.S599QvPhiTauFieldsActual

end
