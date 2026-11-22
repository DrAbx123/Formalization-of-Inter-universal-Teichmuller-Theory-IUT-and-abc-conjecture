import tmp.sheaf.xif.paper.S563QvOrderElementConstructionActual
import tmp.sheaf.xif.paper.S550QvPhiPreFrobenioidActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000

namespace LeanFormal.IUT.XiFPaper.S568QvPhiQOrderTauActual

open CategoryTheory
open Iut
open LeanFormal.IUT.XiFPaper.S432SmallModelActual
open LeanFormal.IUT.XiFPaper.S511PhiCvCandidateActual
open LeanFormal.IUT.XiFPaper.S522QvPhiRamificationModelActual
open LeanFormal.IUT.XiFPaper.S550QvPhiPreFrobenioidActual
open LeanFormal.IUT.XiFPaper.S563QvOrderElementConstructionActual
open Iut.SourceModelFrobenioid

universe u
variable {K : Type u} [Field K]
variable (R : RamificationIndexData (K := K))
variable (data : Input (qvPhi (K := K) R))

/-- Per-object S563 qOrder/pi fields plus the compatibility laws. -/
structure QvPhiQOrderTauInput where
  fields : ∀ X : (qvPreFrobenioid (K := K) R data).IsotropicLinearObject,
    QvPhiQOrderFields (K := K) R data X.obj
  pullback_mem :
    ∀ {X Y : (qvPreFrobenioid (K := K) R data).IsotropicLinearObject} (f : X ⟶ Y)
      (value : (qvPreFrobenioid (K := K) R data).LinearBaseIdentityEndomorphism Y.obj),
      value ∈ tauOfQOrderFields (K := K) R data Y.obj (fields Y) →
        (qvRationalMonoidTransport (K := K) R data).pullback f value ∈
          tauOfQOrderFields (K := K) R data X.obj (fields X)
  units_commute :
    ∀ (X : (qvPreFrobenioid (K := K) R data).IsotropicLinearObject)
      (unit : Units ((qvPreFrobenioid (K := K) R data).LinearBaseIdentityEndomorphism X.obj))
      (characteristic : tauOfQOrderFields (K := K) R data X.obj (fields X)),
      Commute (unit : (qvPreFrobenioid (K := K) R data).LinearBaseIdentityEndomorphism X.obj)
        characteristic.1
  multiplication_bijective :
    ∀ X : (qvPreFrobenioid (K := K) R data).IsotropicLinearObject,
      Function.Bijective
        (fun pair : Units ((qvPreFrobenioid (K := K) R data).LinearBaseIdentityEndomorphism X.obj) ×
          tauOfQOrderFields (K := K) R data X.obj (fields X) =>
          (pair.1 : (qvPreFrobenioid (K := K) R data).LinearBaseIdentityEndomorphism X.obj) * pair.2.1)
  isotropicHull_mem_range :
    ∀ (A : Carrier (qvPhi (K := K) R) data)
      (hull : (qvPreFrobenioid (K := K) R data).IsotropicHull A)
      (characteristic : tauOfQOrderFields (K := K) R data hull.hull (fields { obj := hull.hull, isotropic := hull.isotropic })),
      characteristic.1 ∈ Set.range
        ((qvRationalMonoidTransport (K := K) R data).hullInclusion A hull)

noncomputable def tauDataOfQOrderInput
    (P : QvPhiQOrderTauInput (K := K) R data) : QvPhiTauData (K := K) R data where
  tau X := tauOfQOrderFields (K := K) R data X.obj (P.fields X)
  pullback_mem := P.pullback_mem
  units_commute := P.units_commute
  multiplication_bijective := P.multiplication_bijective
  isotropicHull_mem_range := P.isotropicHull_mem_range

noncomputable def characteristicSplittingOfQOrderInput
    (P : QvPhiQOrderTauInput (K := K) R data) :
    (qvPreFrobenioid (K := K) R data).CharacteristicSplitting
      (qvRationalMonoidTransport (K := K) R data) :=
  characteristicSplittingOfTauData (K := K) R data (tauDataOfQOrderInput (K := K) R data P)

/-- Exact remaining unit decomposition gap: every O^triangle element is uniquely
unit times a power of the S563 pi element. -/
structure QvPhiUnitDecompositionGap
    (F : QvPhiQOrderFields (K := K) R data A) where
  unit_part : (qvPreFrobenioid (K := K) R data).LinearBaseIdentityEndomorphism A
  exponent : ℕ
  decomposition : unit_part =
    qOrderEndomorphismOfFields (K := K) R data A F ^ exponent
  unique : ∀ (u : Units ((qvPreFrobenioid (K := K) R data).LinearBaseIdentityEndomorphism A))
    (n : ℕ), (↑u : (qvPreFrobenioid (K := K) R data).LinearBaseIdentityEndomorphism A) *
      qOrderEndomorphismOfFields (K := K) R data A F ^ n = unit_part → n = exponent

def QvPhiQOrderTauInputRequired : Prop :=
  Nonempty (QvPhiQOrderTauInput (K := K) R data)

end LeanFormal.IUT.XiFPaper.S568QvPhiQOrderTauActual

end
