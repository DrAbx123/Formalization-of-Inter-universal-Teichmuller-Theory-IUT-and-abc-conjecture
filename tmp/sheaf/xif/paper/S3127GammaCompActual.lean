import tmp.sheaf.xif.paper.S3127GammaActionActual
import Mathlib.CategoryTheory.Endomorphism
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3127FreeQuotientActual
open LeanFormal.IUT.XiFPaper.S3127GammaActionActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127GammaCompActual
variable {G : Type} [Group G]

theorem gammaAut_comp {Y : Scheme} (e f : Y ≅ Y) :
    gammaAut (e.trans f) = gammaAut e * gammaAut f := by
  apply RingEquiv.ext
  intro x
  change (Scheme.Γ.map (f.op.hom ≫ e.op.hom)).hom x =
    (Scheme.Γ.map e.op.hom).hom ((Scheme.Γ.map f.op.hom).hom x)
  rw [Scheme.Γ.map_comp, CommRingCat.hom_comp, RingHom.comp_apply]

theorem gammaAut_one (Y : Scheme) :
    gammaAut (Iso.refl Y) = 1 := by
  apply RingEquiv.ext
  intro x
  change (Scheme.Γ.map (𝟙 (Opposite.op Y))).hom x = x
  rw [Scheme.Γ.map_id]
  rfl

noncomputable def gammaActionHom {Y : Scheme} (act : G →* Aut Y) :
    G →* (Scheme.Γ.obj (Opposite.op Y) ≃+* Scheme.Γ.obj (Opposite.op Y)) where
  toFun g := gammaAut ((((act g : Aut Y) : Y ≅ Y)).symm)
  map_one' := by
    rw [map_one act]
    change gammaAut (Iso.refl Y) = 1
    rw [gammaAut_one]
  map_mul' g h := by
    rw [map_mul act]
    change gammaAut ((((act g * act h : Aut Y) : Y ≅ Y)).symm) =
      gammaAut ((((act g : Aut Y) : Y ≅ Y)).symm) *
        gammaAut ((((act h : Aut Y) : Y ≅ Y)).symm)
    rw [Aut.Aut_mul_def, Iso.trans_symm, gammaAut_comp]

noncomputable def gammaMulSemiringAction {Y : Scheme} (act : G →* Aut Y) :
    MulSemiringAction G (Scheme.Γ.obj (Opposite.op Y)) where
  smul g x := (gammaActionHom (Y := Y) act g) x
  one_smul x := by
    change (gammaActionHom (Y := Y) act 1) x = x
    rw [map_one (gammaActionHom (Y := Y) act)]
    rfl
  mul_smul g h x := by
    change (gammaActionHom (Y := Y) act (g * h)) x =
      (gammaActionHom (Y := Y) act g)
        ((gammaActionHom (Y := Y) act h) x)
    rw [map_mul (gammaActionHom (Y := Y) act)]
    rfl
  smul_zero g := map_zero (gammaActionHom (Y := Y) act g)
  smul_add g x y := map_add (gammaActionHom (Y := Y) act g) x y
  smul_one g := map_one (gammaActionHom (Y := Y) act g)
  smul_mul g x y := map_mul (gammaActionHom (Y := Y) act g) x y

#check gammaMulSemiringAction
#check gammaActionHom
#check gammaAut_comp
#check gammaAut_one
end LeanFormal.IUT.XiFPaper.S3127GammaCompActual
end
