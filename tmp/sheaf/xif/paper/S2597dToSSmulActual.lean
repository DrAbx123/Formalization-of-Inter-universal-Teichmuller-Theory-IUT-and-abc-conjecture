import tmp.sheaf.xif.paper.S2597cIntegralActual
import tmp.sheaf.xif.paper.S2596qNaturalActual
import tmp.sheaf.xif.paper.S2597RootSetEquivActual

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
open Polynomial NumberField

namespace LeanFormal.IUT.XiFPaper.S2597dToSSmulActual

abbrev Cb : Type := LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual.C
abbrev Sb : Type := LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual.S
abbrev Fb : Type := LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual.S1720Field
abbrev Lb : Type := LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual.S2057FiveDivisionField
abbrev OLb : Type := LeanFormal.IUT.XiFPaper.S2594LP0PActual.OL
abbrev Tb : Type := LeanFormal.IUT.XiFPaper.S2594LP0PActual.T
abbrev Tb' : Type := LeanFormal.IUT.XiFPaper.S2610TTPrimeActual.T'

section Main

local instance (priority := 1100) : SMul Cb OLb := Algebra.toSMul
local instance (priority := 1100) : SMul Cb Fb := Algebra.toSMul
local instance (priority := 1100) : SMul Cb Lb := Algebra.toSMul
local instance (priority := 1100) : SMul Cb Sb := Algebra.toSMul
local instance (priority := 1100) : SMul Cb Tb' := Algebra.toSMul
local instance (priority := 1100) : SMul OLb Lb := Algebra.toSMul
local instance (priority := 1100) : SMul OLb Tb' := Algebra.toSMul
local instance (priority := 1100) : SMul Sb Fb := Algebra.toSMul
local instance (priority := 1100) : SMul Sb Lb := Algebra.toSMul
local instance (priority := 1100) : SMul Sb Tb' := Algebra.toSMul
local instance (priority := 1100) : SMul Tb' Lb := Algebra.toSMul
local instance (priority := 1100) : SMul Fb Lb := Algebra.toSMul

/-! ## Towers and basic instances for the S2597 variables -/

local instance tower_Cb_Sb_Fb : IsScalarTower Cb Sb Fb :=
  IsScalarTower.of_algebraMap_eq'
    LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual.liftCL_comp.symm

local instance tower_Sb_Fb_Lb : IsScalarTower Sb Fb Lb :=
  IsScalarTower.of_algebraMap_eq'
    LeanFormal.IUT.XiFPaper.S2597bTowersActual.algMap_Sb_Fb_Lb_comp

local instance tower_Cb_OLb_Lb2 : IsScalarTower Cb OLb Lb :=
  LeanFormal.IUT.XiFPaper.S2597cIntegralActual.tower_Cb_OLb_Lb

local instance tower_OLb_Tb'_Lb2 : IsScalarTower OLb Tb' Lb :=
  LeanFormal.IUT.XiFPaper.S2597cIntegralActual.tower_OLb_Tb'_Lb

local instance tower_Sb_Tb'_Lb2 : IsScalarTower Sb Tb' Lb :=
  LeanFormal.IUT.XiFPaper.S2597cIntegralActual.tower_Sb_Tb'_Lb

local instance tower_Cb_Sb_Tb'2 : IsScalarTower Cb Sb Tb' :=
  LeanFormal.IUT.XiFPaper.S2597cIntegralActual.tower_Cb_Sb_Tb'

local instance tower_Cb_OLb_Tb'2 : IsScalarTower Cb OLb Tb' :=
  LeanFormal.IUT.XiFPaper.S2597cIntegralActual.tower_Cb_OLb_Tb'

local instance tower_Cb_Sb_Lb2 : IsScalarTower Cb Sb Lb :=
  LeanFormal.IUT.XiFPaper.S2597cIntegralActual.tower_Cb_Sb_Lb

local instance instIsDomainSb : IsDomain Sb :=
  IsLocalization.isDomain_of_le_nonZeroDivisors (M := Submonoid.powers
    (LeanFormal.IUT.XiFPaper.S2562HZcMonicCActual.Cden : Cb)) Sb
    ((Submonoid.powers_le).mpr (mem_nonZeroDivisors_of_ne_zero
      LeanFormal.IUT.XiFPaper.S2605LiftSLActual.Cden_Cb_ne_zero))

local instance instIsDomainTb' : IsDomain Tb' :=
  IsLocalization.isDomain_of_le_nonZeroDivisors (M := LeanFormal.IUT.XiFPaper.S2610TTPrimeActual.MT) Tb' (by
    rw [← LeanFormal.IUT.XiFPaper.S2610TTPrimeActual.hMT]
    exact LeanFormal.IUT.XiFPaper.S2603LiftTLInjectiveActual.powers_r_nonZeroDivisors)

local instance instIsFractionRingSbFb : IsFractionRing Sb Fb :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (Submonoid.powers (LeanFormal.IUT.XiFPaper.S2562HZcMonicCActual.Cden : Cb)) Sb Fb

local instance instIsFractionRingTb'Lb : IsFractionRing Tb' Lb :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (Algebra.algebraMapSubmonoid OLb
      (Submonoid.powers (LeanFormal.IUT.XiFPaper.S2562HZcMonicCActual.Cden : Cb))) Tb' Lb

local instance instFaithfulSMulSbLb : FaithfulSMul Sb Lb :=
  (faithfulSMul_iff_algebraMap_injective Sb Lb).mpr (by
    rw [show algebraMap Sb Lb = (algebraMap Fb Lb).comp (algebraMap Sb Fb) from rfl]
    exact (FaithfulSMul.algebraMap_injective Fb Lb).comp (IsFractionRing.injective Sb Fb))

/-! ## The Galois action on T' -/

noncomputable def sigmaRingEquivT' (sigma : Gal(Lb/Fb)) : Tb' ≃+* Tb' :=
  (LeanFormal.IUT.XiFPaper.S2610TTPrimeActual.eTT'.symm.trans
    (LeanFormal.IUT.XiFPaper.S2596eSigmaEquivHomActual.sigmaRingEquiv sigma)).trans
    LeanFormal.IUT.XiFPaper.S2610TTPrimeActual.eTT'

lemma sigmaRingEquivT'_apply (sigma : Gal(Lb/Fb)) (y : Tb') :
    sigmaRingEquivT' sigma y = LeanFormal.IUT.XiFPaper.S2610TTPrimeActual.eTT'
      (LeanFormal.IUT.XiFPaper.S2596eSigmaEquivHomActual.sigmaRingEquiv sigma
        (LeanFormal.IUT.XiFPaper.S2610TTPrimeActual.eTT'.symm y)) := rfl

lemma sigmaRingEquivT'_one : sigmaRingEquivT' (1 : Gal(Lb/Fb)) = 1 := by
  refine RingEquiv.ext fun y => ?_
  rw [sigmaRingEquivT'_apply]
  rw [LeanFormal.IUT.XiFPaper.S2596eSigmaEquivHomActual.sigmaRingEquiv_one]
  simp

lemma sigmaRingEquivT'_mul (s t : Gal(Lb/Fb)) :
    sigmaRingEquivT' (s * t) = sigmaRingEquivT' s * sigmaRingEquivT' t := by
  refine RingEquiv.ext fun y => ?_
  simp only [sigmaRingEquivT'_apply, RingAut.mul_apply,
    LeanFormal.IUT.XiFPaper.S2596eSigmaEquivHomActual.sigmaRingEquiv_mul]
  simp

noncomputable def sigmaEquivHomT' : Gal(Lb/Fb) →* (Tb' ≃+* Tb') where
  toFun := sigmaRingEquivT'
  map_one' := sigmaRingEquivT'_one
  map_mul' := sigmaRingEquivT'_mul

noncomputable instance instRingEquivActionT' : MulSemiringAction (Tb' ≃+* Tb') Tb' where
  smul e t := e t
  one_smul t := rfl
  mul_smul e f t := rfl
  smul_zero e := map_zero e
  smul_add e := map_add e
  smul_mul e := map_mul e
  smul_one e := map_one e

noncomputable instance instGalActionT' : MulSemiringAction (Gal(Lb/Fb)) Tb' :=
  MulSemiringAction.compHom Tb' sigmaEquivHomT'

/-! ## Compatibility of the Galois action with the algebra map to L -/

lemma eSigma_fixes_algebraMap (sigma : Gal(Lb/Fb)) (c : Cb) :
    LeanFormal.IUT.XiFPaper.S2596eSigmaEquivHomActual.eSigma sigma (algebraMap Cb OLb c) =
      algebraMap Cb OLb c := by
  change galRestrict Cb Fb Lb OLb sigma (algebraMap Cb OLb c) = algebraMap Cb OLb c
  exact (galRestrict Cb Fb Lb OLb sigma).commutes c

lemma algebraMap_T'_smul (sigma : Gal(Lb/Fb)) (y : Tb') :
    algebraMap Tb' Lb (sigma • y) = sigma • (algebraMap Tb' Lb y) := by
  change LeanFormal.IUT.XiFPaper.S2599TInstancesActual.liftTL
      (LeanFormal.IUT.XiFPaper.S2610TTPrimeActual.eTT'.symm
        (LeanFormal.IUT.XiFPaper.S2610TTPrimeActual.eTT'
          (LeanFormal.IUT.XiFPaper.S2596eSigmaEquivHomActual.sigmaRingEquiv sigma
            (LeanFormal.IUT.XiFPaper.S2610TTPrimeActual.eTT'.symm y)))) =
    sigma (LeanFormal.IUT.XiFPaper.S2599TInstancesActual.liftTL
      (LeanFormal.IUT.XiFPaper.S2610TTPrimeActual.eTT'.symm y))
  rw [RingEquiv.symm_apply_apply]
  exact LeanFormal.IUT.XiFPaper.S2596qNaturalActual.algebraMap_smul_T sigma
    (LeanFormal.IUT.XiFPaper.S2610TTPrimeActual.eTT'.symm y)

/-! ## The Galois action fixes the image of S -/

lemma sigmaRingEquiv_fixes_liftST (sigma : Gal(Lb/Fb)) :
    (LeanFormal.IUT.XiFPaper.S2596eSigmaEquivHomActual.sigmaRingEquiv sigma).toRingHom.comp
        LeanFormal.IUT.XiFPaper.S2599TInstancesActual.liftST =
      LeanFormal.IUT.XiFPaper.S2599TInstancesActual.liftST := by
  apply IsLocalization.ringHom_ext (M := Algebra.algebraMapSubmonoid Cb
    (Submonoid.powers (LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual.c : ℤ)))
  ext c
  change LeanFormal.IUT.XiFPaper.S2596eSigmaEquivHomActual.sigmaRingEquiv sigma
      (LeanFormal.IUT.XiFPaper.S2599TInstancesActual.liftST (algebraMap Cb Sb c)) =
    LeanFormal.IUT.XiFPaper.S2599TInstancesActual.liftST (algebraMap Cb Sb c)
  rw [show LeanFormal.IUT.XiFPaper.S2599TInstancesActual.liftST (algebraMap Cb Sb c) =
    LeanFormal.IUT.XiFPaper.S2599TInstancesActual.gCT c from
    RingHom.congr_fun LeanFormal.IUT.XiFPaper.S2597bTowersActual.liftST_comp c]
  rw [show LeanFormal.IUT.XiFPaper.S2599TInstancesActual.gCT c =
    algebraMap OLb Tb (algebraMap Cb OLb c) from rfl]
  rw [LeanFormal.IUT.XiFPaper.S2596eSigmaEquivHomActual.sigmaRingEquiv_apply_algebraMap]
  rw [eSigma_fixes_algebraMap]

lemma sigmaRingEquivT'_fixes_liftST' (sigma : Gal(Lb/Fb)) :
    (sigmaRingEquivT' sigma).toRingHom.comp
        LeanFormal.IUT.XiFPaper.S2597bTowersActual.liftST' =
      LeanFormal.IUT.XiFPaper.S2597bTowersActual.liftST' := by
  apply IsLocalization.ringHom_ext (M := Algebra.algebraMapSubmonoid Cb
    (Submonoid.powers (LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual.c : ℤ)))
  ext c
  change sigmaRingEquivT' sigma
      (LeanFormal.IUT.XiFPaper.S2597bTowersActual.liftST' (algebraMap Cb Sb c)) =
    LeanFormal.IUT.XiFPaper.S2597bTowersActual.liftST' (algebraMap Cb Sb c)
  rw [show LeanFormal.IUT.XiFPaper.S2597bTowersActual.liftST' (algebraMap Cb Sb c) =
    LeanFormal.IUT.XiFPaper.S2597bTowersActual.gCT' c from
    RingHom.congr_fun LeanFormal.IUT.XiFPaper.S2597bTowersActual.liftST'_comp c]
  rw [show LeanFormal.IUT.XiFPaper.S2597bTowersActual.gCT' c =
    algebraMap OLb Tb' (algebraMap Cb OLb c) from rfl]
  rw [sigmaRingEquivT'_apply]
  rw [LeanFormal.IUT.XiFPaper.S2597bTowersActual.eTT'_symm_algebraMap]
  rw [LeanFormal.IUT.XiFPaper.S2596eSigmaEquivHomActual.sigmaRingEquiv_apply_algebraMap]
  rw [eSigma_fixes_algebraMap]
  rw [LeanFormal.IUT.XiFPaper.S2597bTowersActual.eTT'_algebraMap]

lemma fix_Sb (sigma : Gal(Lb/Fb)) (a : Sb) :
    sigma • (algebraMap Sb Tb' a) = algebraMap Sb Tb' a := by
  change sigmaRingEquivT' sigma (LeanFormal.IUT.XiFPaper.S2597bTowersActual.liftST' a) =
    LeanFormal.IUT.XiFPaper.S2597bTowersActual.liftST' a
  exact RingHom.congr_fun (sigmaRingEquivT'_fixes_liftST' sigma) a

local instance smulCommClass_Gal_Sb_Tb' : SMulCommClass (Gal(Lb/Fb)) Sb Tb' where
  smul_comm sigma a y := by
    rw [Algebra.smul_def]
    rw [MulSemiringAction.smul_mul]
    rw [fix_Sb]
    rw [Algebra.smul_def]

/-! ## toS_smul -/

theorem toS_smul (f : Sb[X]) (hmonic : f.Monic) (hdeg : f.natDegree ≠ 0)
    (sigma : Gal(Lb/Fb)) (x : f.rootSet Lb) :
    LeanFormal.IUT.XiFPaper.S2597RootSetEquivActual.toS (R := Sb) (S := Tb')
        (L := Lb) f hmonic hdeg (sigma • x) =
      sigma • LeanFormal.IUT.XiFPaper.S2597RootSetEquivActual.toS (R := Sb) (S := Tb')
        (L := Lb) f hmonic hdeg x := by
  apply Subtype.ext
  apply IsFractionRing.injective Tb' Lb
  rw [LeanFormal.IUT.XiFPaper.S2597RootSetEquivActual.toS_val]
  rw [rootSet.coe_smul]
  rw [rootSet.coe_smul]
  rw [algebraMap_T'_smul]
  rw [LeanFormal.IUT.XiFPaper.S2597RootSetEquivActual.toS_val]

end Main

#print axioms toS_smul

end LeanFormal.IUT.XiFPaper.S2597dToSSmulActual
end