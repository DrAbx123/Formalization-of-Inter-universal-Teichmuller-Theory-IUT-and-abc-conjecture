import tmp.sheaf.xif.paper.S3127GammaCommActual
import tmp.sheaf.xif.paper.S3127GammaAlgebraActual
import Mathlib.AlgebraicGeometry.AffineScheme
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S3127GammaAlgebraActual
open LeanFormal.IUT.XiFPaper.S3127GammaActionActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127GammaBridgeActual
variable {K : Type} [Field K]

theorem S3127ToSpecGamma_bridge (Y : SchemeOverField K) [IsAffine Y.left] :
    Y.left.isoSpec.hom ≫
      Spec.map (CommRingCat.ofHom (gammaAlgebraMap Y)) = Y.hom := by
  have hnat := Scheme.isoSpec_hom_naturality (X := Y.left)
    (Y := Spec (CommRingCat.of K)) Y.hom
  rw [Scheme.isoSpec_Spec_hom] at hnat
  have hcomp : (Scheme.ΓSpecIso (CommRingCat.of K)).hom ≫
      CommRingCat.ofHom (gammaAlgebraMap Y) = Scheme.Γ.map Y.hom.op := by
    rw [show CommRingCat.ofHom (gammaAlgebraMap Y) =
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ Scheme.Γ.map Y.hom.op from rfl]
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  have happ : Y.hom.appTop = Scheme.Γ.map Y.hom.op := rfl
  have hcomp' := congrArg Spec.map hcomp
  erw [Spec.map_comp] at hcomp'
  rw [← happ] at hcomp'
  have hmap : Spec.map Y.hom.appTop =
      Spec.map (CommRingCat.ofHom (gammaAlgebraMap Y)) ≫
        Spec.map (Scheme.ΓSpecIso (CommRingCat.of K)).hom := hcomp'.symm
  rw [hmap] at hnat
  refine (cancel_mono (Spec.map (Scheme.ΓSpecIso (CommRingCat.of K)).hom)).mp ?_
  change ((Over.left Y).isoSpec.hom ≫
      Spec.map (CommRingCat.ofHom (gammaAlgebraMap Y))) ≫
        Spec.map (Scheme.ΓSpecIso (CommRingCat.of K)).hom =
    Over.hom Y ≫ Spec.map (Scheme.ΓSpecIso (CommRingCat.of K)).hom
  exact hnat


#check S3127ToSpecGamma_bridge
end LeanFormal.IUT.XiFPaper.S3127GammaBridgeActual
end
