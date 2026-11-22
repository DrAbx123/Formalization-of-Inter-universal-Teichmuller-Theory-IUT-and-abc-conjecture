import tmp.sheaf.xif.paper.S550QvPhiPreFrobenioidActual

-- S555 audit: exact tau generator data for S550.  qvPhiRamificationModel
-- contains ramification indices e but no qOrder/pi element and no canonical
-- map to O^triangle; the tau laws are recorded exactly.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S555QvPhiTauConstructionGapActual

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
variable (data : Input (qvPhi (K := K) R))

abbrev QvP := qvPreFrobenioid (K := K) R data
abbrev QvR := qvRationalMonoidTransport (K := K) R data

structure QvPhiTauGlobalGeneratorData where
  qOrderElement : ∀ X : PreFrobenioid.IsotropicLinearObject (P := QvP R data),
    PreFrobenioid.LinearBaseIdentityEndomorphism (P := QvP R data) X.obj
  piElement : ∀ X : PreFrobenioid.IsotropicLinearObject (P := QvP R data),
    PreFrobenioid.LinearBaseIdentityEndomorphism (P := QvP R data) X.obj
  tau : ∀ X : PreFrobenioid.IsotropicLinearObject (P := QvP R data),
    Submonoid (PreFrobenioid.LinearBaseIdentityEndomorphism (P := QvP R data) X.obj)
  tau_eq_zpowers_qOrder : Prop
  pullback_mem :
    ∀ {X Y : PreFrobenioid.IsotropicLinearObject (P := QvP R data)} (f : X ⟶ Y)
      (value : PreFrobenioid.LinearBaseIdentityEndomorphism (P := QvP R data) Y.obj),
      value ∈ tau Y →
        (QvR R data).pullback f value ∈ tau X
  units_commute :
    ∀ (X : PreFrobenioid.IsotropicLinearObject (P := QvP R data))
      (unit : Units (PreFrobenioid.LinearBaseIdentityEndomorphism (P := QvP R data) X.obj))
      (characteristic : tau X),
      Commute (unit : PreFrobenioid.LinearBaseIdentityEndomorphism (P := QvP R data) X.obj)
        characteristic.1
  multiplication_bijective :
    ∀ X : PreFrobenioid.IsotropicLinearObject (P := QvP R data),
      Function.Bijective
        (fun pair : Units (PreFrobenioid.LinearBaseIdentityEndomorphism (P := QvP R data) X.obj) × tau X =>
          (pair.1 : PreFrobenioid.LinearBaseIdentityEndomorphism (P := QvP R data) X.obj) * pair.2.1)
  isotropicHull_mem_range :
    ∀ (A : SourceModelFrobenioid.Carrier (qvPhi (K := K) R) data)
      (hull : PreFrobenioid.IsotropicHull (P := QvP R data) A)
      (characteristic : tau { obj := hull.hull, isotropic := hull.isotropic }),
      characteristic.1 ∈ Set.range ((QvR R data).hullInclusion A hull)

noncomputable def qvPhiTauDataOfGenerator
    (D : QvPhiTauGlobalGeneratorData (K := K) R data) :
    QvPhiTauData (K := K) R data where
  tau := D.tau
  pullback_mem := D.pullback_mem
  units_commute := D.units_commute
  multiplication_bijective := D.multiplication_bijective
  isotropicHull_mem_range := D.isotropicHull_mem_range

noncomputable def characteristicSplittingOfGenerator
    (D : QvPhiTauGlobalGeneratorData (K := K) R data) :
    (QvP R data).CharacteristicSplitting (QvR R data) :=
  characteristicSplittingOfTauData R data
    (qvPhiTauDataOfGenerator (K := K) R data D)

#check qvPreFrobenioid
#check qvRationalMonoidTransport
#check QvPhiTauGlobalGeneratorData
#check qvPhiTauDataOfGenerator
#check characteristicSplittingOfGenerator

end LeanFormal.IUT.XiFPaper.S555QvPhiTauConstructionGapActual

end