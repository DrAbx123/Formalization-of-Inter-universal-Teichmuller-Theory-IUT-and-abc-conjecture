import tmp.sheaf.xif.paper.S2597bTowersActual

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
open Polynomial NumberField

namespace LeanFormal.IUT.XiFPaper.S2597cIntegralActual

abbrev Cb : Type := LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual.C
abbrev Sb : Type := LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual.S
abbrev Fb : Type := LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual.S1720Field
abbrev Lb : Type := LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual.S2057FiveDivisionField
abbrev OLb : Type := LeanFormal.IUT.XiFPaper.S2594LP0PActual.OL
abbrev Tb : Type := LeanFormal.IUT.XiFPaper.S2594LP0PActual.T
abbrev Tb' : Type := LeanFormal.IUT.XiFPaper.S2610TTPrimeActual.T'

/-!
## The SMul interface

The SplittingField and OreLocalization derived SMul instances are propositionally
but not definitionally equal to the algebra SMuls.  All towers below are therefore
stated with the canonical algebra SMuls, installed locally at high priority.
-/

section TowerFix

local instance (priority := 1100) : SMul Cb OLb := Algebra.toSMul
local instance (priority := 1100) : SMul Cb Fb := Algebra.toSMul
local instance (priority := 1100) : SMul Cb Lb := Algebra.toSMul
local instance (priority := 1100) : SMul Cb Sb := Algebra.toSMul
local instance (priority := 1100) : SMul Cb Tb' := Algebra.toSMul
local instance (priority := 1100) : SMul Cb Tb := Algebra.toSMul
local instance (priority := 1100) : SMul OLb Lb := Algebra.toSMul
local instance (priority := 1100) : SMul OLb Tb' := Algebra.toSMul
local instance (priority := 1100) : SMul OLb Tb := Algebra.toSMul
local instance (priority := 1100) : SMul Sb Fb := Algebra.toSMul
local instance (priority := 1100) : SMul Sb Lb := Algebra.toSMul
local instance (priority := 1100) : SMul Sb Tb' := Algebra.toSMul
local instance (priority := 1100) : SMul Tb' Lb := Algebra.toSMul
local instance (priority := 1100) : SMul Fb Lb := Algebra.toSMul

lemma tower_Cb_OLb_Lb : IsScalarTower Cb OLb Lb :=
  IsScalarTower.of_algebraMap_eq'
    LeanFormal.IUT.XiFPaper.S2597bTowersActual.algMap_Cb_OLb_Lb_comp

lemma tower_Cb_Sb_Tb' : IsScalarTower Cb Sb Tb' :=
  IsScalarTower.of_algebraMap_eq'
    LeanFormal.IUT.XiFPaper.S2597bTowersActual.algMap_Cb_Sb_Tb'_comp

lemma tower_Cb_OLb_Tb' : IsScalarTower Cb OLb Tb' :=
  IsScalarTower.of_algebraMap_eq'
    LeanFormal.IUT.XiFPaper.S2597bTowersActual.algMap_Cb_OLb_Tb'_comp

lemma tower_Cb_Sb_Lb : IsScalarTower Cb Sb Lb :=
  IsScalarTower.of_algebraMap_eq'
    LeanFormal.IUT.XiFPaper.S2597bTowersActual.algMap_Cb_Sb_Lb_comp

lemma tower_OLb_Tb'_Lb : IsScalarTower OLb Tb' Lb :=
  IsScalarTower.of_algebraMap_eq'
    LeanFormal.IUT.XiFPaper.S2597bTowersActual.algMap_OLb_Tb'_Lb_comp

lemma tower_Sb_Tb'_Lb : IsScalarTower Sb Tb' Lb :=
  IsScalarTower.of_algebraMap_eq'
    LeanFormal.IUT.XiFPaper.S2597bTowersActual.algMap_Sb_Tb'_Lb_comp

noncomputable instance instIsIntegralClosureT' : IsIntegralClosure Tb' Sb Lb :=
  LeanFormal.IUT.XiFPaper.S2536LocalizedPowersActual.isIntegralClosure_localization_powers
    (A := Cb) (C := OLb) (K := Fb) (L := Lb) (R := Sb) (S := Tb')
    (a := (LeanFormal.IUT.XiFPaper.S2562HZcMonicCActual.Cden : Cb))
    (mem_nonZeroDivisors_of_ne_zero
      (Int.cast_ne_zero.mpr LeanFormal.IUT.XiFPaper.S2562HZcMonicCActual.Cden_ne_zero))
    (hACL := tower_Cb_OLb_Lb)
    (hARS := tower_Cb_Sb_Tb')
    (hACS := tower_Cb_OLb_Tb')
    (hARL := tower_Cb_Sb_Lb)
    (hCSL := tower_OLb_Tb'_Lb)
    (hRSL := tower_Sb_Tb'_Lb)

end TowerFix

#print axioms tower_Cb_OLb_Lb
#print axioms tower_Cb_Sb_Tb'
#print axioms tower_Cb_OLb_Tb'
#print axioms tower_Cb_Sb_Lb
#print axioms tower_OLb_Tb'_Lb
#print axioms tower_Sb_Tb'_Lb
#print axioms instIsIntegralClosureT'

end LeanFormal.IUT.XiFPaper.S2597cIntegralActual
end
