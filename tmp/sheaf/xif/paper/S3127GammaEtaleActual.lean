import tmp.sheaf.xif.paper.S3127GammaBridgeActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S3127GammaBridgeActual
open LeanFormal.IUT.XiFPaper.S3127GammaAlgebraActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127GammaEtaleActual
variable {K : Type} [Field K]

theorem S3127Gamma_specMap_eq (Y : SchemeOverField K) [IsAffine Y.left] :
    Spec.map (CommRingCat.ofHom (gammaAlgebraMap Y)) =
      Y.left.isoSpec.inv ≫ Y.hom := by
  rw [← S3127ToSpecGamma_bridge Y]
  rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  rfl

theorem S3127GammaAlgebra_etale (Y : SchemeOverField K) [IsAffine Y.left]
    (h : Etale Y.hom) : Algebra.Etale K (Scheme.Γ.obj (Opposite.op Y.left)) := by
  have hspec := S3127Gamma_specMap_eq Y
  have het : Etale (Spec.map (CommRingCat.ofHom (gammaAlgebraMap Y))) := by
    rw [hspec]
    exact (MorphismProperty.cancel_left_of_respectsIso (P := @Etale)
      Y.left.isoSpec.inv Y.hom).mpr h
  have hEt : (CommRingCat.Hom.hom (CommRingCat.ofHom (gammaAlgebraMap Y))).Etale :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mp het
  simpa using (RingHom.etale_algebraMap (R := K) (S := Scheme.Γ.obj (Opposite.op Y.left))).mp hEt

theorem S3127GammaAlgebra_finite (Y : SchemeOverField K) [IsAffine Y.left]
    (h : IsFinite Y.hom) : Module.Finite K (Scheme.Γ.obj (Opposite.op Y.left)) := by
  have hspec := S3127Gamma_specMap_eq Y
  have hfin : IsFinite (Spec.map (CommRingCat.ofHom (gammaAlgebraMap Y))) := by
    rw [hspec]
    exact (MorphismProperty.cancel_left_of_respectsIso (P := @IsFinite)
      Y.left.isoSpec.inv Y.hom).mpr h
  have hFin : (CommRingCat.Hom.hom (CommRingCat.ofHom (gammaAlgebraMap Y))).Finite :=
    (AlgebraicGeometry.IsFinite.SpecMap_iff (CommRingCat.ofHom (gammaAlgebraMap Y))).mp hfin
  simpa using (RingHom.finite_algebraMap (A := K) (B := Scheme.Γ.obj (Opposite.op Y.left))).mp hFin

#check S3127GammaAlgebra_etale
#check S3127GammaAlgebra_finite
end LeanFormal.IUT.XiFPaper.S3127GammaEtaleActual
end
