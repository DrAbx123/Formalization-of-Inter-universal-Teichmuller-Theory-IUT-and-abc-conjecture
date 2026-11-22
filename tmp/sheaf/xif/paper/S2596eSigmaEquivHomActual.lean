import tmp.sheaf.xif.paper.S2596dSigmaRingEquivActual
noncomputable section
set_option autoImplicit false
open Polynomial NumberField
namespace LeanFormal.IUT.XiFPaper.S2596eSigmaEquivHomActual
open LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual
open LeanFormal.IUT.XiFPaper.S2594LP0PActual
open LeanFormal.IUT.XiFPaper.S2562HZcMonicCActual
open LeanFormal.IUT.XiFPaper.S2596dHfixActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
local instance : MulSemiringAction Gal(S2057FiveDivisionField/S1720Field) OL :=
  IsIntegralClosure.MulSemiringAction (RingOfIntegers S1720Field) S1720Field S2057FiveDivisionField (RingOfIntegers S2057FiveDivisionField)
noncomputable def eSigma (sigma : Gal(S2057FiveDivisionField/S1720Field)) : OL ≃+* OL :=
  MulSemiringAction.toRingEquiv (G := Gal(S2057FiveDivisionField/S1720Field)) (R := OL) sigma
lemma eSigma_aOL (sigma : Gal(S2057FiveDivisionField/S1720Field)) : eSigma sigma aOL = aOL := by
  change sigma • aOL = aOL
  exact hfix sigma
lemma hH (sigma : Gal(S2057FiveDivisionField/S1720Field)) :
    Submonoid.map (eSigma sigma).toMonoidHom (Submonoid.powers aOL) = Submonoid.powers aOL := by
  rw [Submonoid.map_powers (eSigma sigma).toMonoidHom aOL]
  change Submonoid.powers ((eSigma sigma) aOL) = Submonoid.powers aOL
  rw [eSigma_aOL sigma]
noncomputable def sigmaRingEquiv (sigma : Gal(S2057FiveDivisionField/S1720Field)) : T ≃+* T :=
  IsLocalization.ringEquivOfRingEquiv
    (M := Submonoid.powers aOL) (S := T) (T := Submonoid.powers aOL) T
    (eSigma sigma) (hH sigma)
lemma sigmaRingEquiv_apply_algebraMap (sigma : Gal(S2057FiveDivisionField/S1720Field)) (x : OL) :
    sigmaRingEquiv sigma (algebraMap OL T x) = algebraMap OL T (eSigma sigma x) :=
  IsLocalization.ringEquivOfRingEquiv_eq (hH sigma) x
lemma sigmaRingEquiv_one : sigmaRingEquiv 1 = 1 := by
  have h : (sigmaRingEquiv 1).toRingHom = RingHom.id T := by
    apply IsLocalization.ringHom_ext (Submonoid.powers aOL)
    ext x
    rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.id_apply]
    change sigmaRingEquiv 1 (algebraMap OL T x) = algebraMap OL T x
    rw [sigmaRingEquiv_apply_algebraMap]
    simp [eSigma]
  ext t
  exact RingHom.congr_fun h t
lemma sigmaRingEquiv_mul (sigma tau) :
    sigmaRingEquiv (sigma * tau) = sigmaRingEquiv sigma * sigmaRingEquiv tau := by
  have h : (sigmaRingEquiv (sigma * tau)).toRingHom =
      (sigmaRingEquiv sigma).toRingHom.comp (sigmaRingEquiv tau).toRingHom := by
    apply IsLocalization.ringHom_ext (Submonoid.powers aOL)
    ext x
    rw [RingHom.comp_apply, RingHom.comp_apply]
    change sigmaRingEquiv (sigma * tau) (algebraMap OL T x) =
      sigmaRingEquiv sigma (sigmaRingEquiv tau (algebraMap OL T x))
    rw [sigmaRingEquiv_apply_algebraMap, sigmaRingEquiv_apply_algebraMap, sigmaRingEquiv_apply_algebraMap]
    simp [eSigma, MonoidHom.map_mul]
  ext t
  exact RingHom.congr_fun h t
#print axioms sigmaRingEquiv_apply_algebraMap
#print axioms sigmaRingEquiv_one
#print axioms sigmaRingEquiv_mul
noncomputable def sigmaEquivHom :
    Gal(S2057FiveDivisionField/S1720Field) →* (T ≃+* T) where
  toFun := sigmaRingEquiv
  map_one' := sigmaRingEquiv_one
  map_mul' := fun sigma tau => sigmaRingEquiv_mul sigma tau
noncomputable instance : MulSemiringAction (T ≃+* T) T where
  smul e t := e t
  one_smul t := rfl
  mul_smul e f t := rfl
  smul_zero e := map_zero e
  smul_add e := map_add e
  smul_mul e := map_mul e
  smul_one e := map_one e
noncomputable instance : MulSemiringAction Gal(S2057FiveDivisionField/S1720Field) T :=
  MulSemiringAction.compHom T sigmaEquivHom
#print axioms sigmaEquivHom
end LeanFormal.IUT.XiFPaper.S2596eSigmaEquivHomActual
end
