import tmp.sheaf.xif.paper.S534QvPhiCvSharpSubmonoidActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

/-! # S540: exact gap from the Phi_Cv^sharp submonoid to CharacteristicSplitting tau

S522's qvPhiRamificationModel is a `DivisorialMonoidOn`, not a
`PreFrobenioid`, and S534's sharp submonoid is a divisor-monoid submonoid,
not a submonoid of `O^triangle`.  The following record states exactly the
missing preFrobenioid/transport/tau/hull data; it is a condition, not a
constructed splitting.
-/

namespace LeanFormal.IUT.XiFPaper.S540QvPhiTauExactGapActual

open CategoryTheory
open Iut

universe u

variable (C : Type u) [Category C]
variable (D : Type u) [Category D]
variable (IsFSM : ∀ {X Y : D}, (X ⟶ Y) → Prop)

/-- Exact missing data for the Qv-Phi CharacteristicSplitting tau part. -/
structure QvPhiTauData where
  preFrobenioid : PreFrobenioid C D IsFSM
  transport : preFrobenioid.RationalMonoidTransport
  tau : ∀ X : preFrobenioid.IsotropicLinearObject,
    Submonoid (preFrobenioid.LinearBaseIdentityEndomorphism X.obj)
  pullback_mem :
    ∀ {X Y : preFrobenioid.IsotropicLinearObject} (f : X ⟶ Y)
      (value : preFrobenioid.LinearBaseIdentityEndomorphism Y.obj),
      value ∈ tau Y → transport.pullback f value ∈ tau X
  units_commute :
    ∀ (X : preFrobenioid.IsotropicLinearObject)
      (unit : Units (preFrobenioid.LinearBaseIdentityEndomorphism X.obj))
      (characteristic : tau X),
      Commute (unit : preFrobenioid.LinearBaseIdentityEndomorphism X.obj)
        characteristic.1
  multiplication_bijective :
    ∀ X : preFrobenioid.IsotropicLinearObject,
      Function.Bijective
        (fun pair : Units (preFrobenioid.LinearBaseIdentityEndomorphism X.obj) × tau X =>
          (pair.1 : preFrobenioid.LinearBaseIdentityEndomorphism X.obj) * pair.2.1)
  isotropicHull_mem_range :
    ∀ (A : C) (hull : preFrobenioid.IsotropicHull A)
      (characteristic : tau { obj := hull.hull, isotropic := hull.isotropic }),
      characteristic.1 ∈ Set.range (transport.hullInclusion A hull)

noncomputable def characteristicSplittingOfQvPhiTauData
    (S : QvPhiTauData C D IsFSM) :
    S.preFrobenioid.CharacteristicSplitting S.transport where
  tau := S.tau
  pullback_mem := S.pullback_mem
  units_commute := S.units_commute
  multiplication_bijective := S.multiplication_bijective
  isotropicHull_mem_range := S.isotropicHull_mem_range

/-- Exact required condition: the missing preFrobenioid/transport/tau/hull data. -/
def QvPhiTauRequired : Prop := Nonempty (QvPhiTauData C D IsFSM)

theorem qvPhiTauRequired_iff :
    QvPhiTauRequired C D IsFSM ↔
      ∃ (P : PreFrobenioid C D IsFSM) (R : P.RationalMonoidTransport),
        Nonempty (P.CharacteristicSplitting R) := by
  constructor
  · rintro ⟨S⟩
    exact ⟨S.preFrobenioid, S.transport,
      ⟨characteristicSplittingOfQvPhiTauData C D IsFSM S⟩⟩
  · rintro ⟨P, R, ⟨S⟩⟩
    exact ⟨{ preFrobenioid := P
             transport := R
             tau := S.tau
             pullback_mem := S.pullback_mem
             units_commute := S.units_commute
             multiplication_bijective := S.multiplication_bijective
             isotropicHull_mem_range := S.isotropicHull_mem_range }⟩

end LeanFormal.IUT.XiFPaper.S540QvPhiTauExactGapActual

end
