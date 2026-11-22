import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
noncomputable section
open CategoryTheory AlgebraicGeometry
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127GammaRAlgebraActual
variable {R : Type} [CommRing R]

noncomputable def gammaAlgebraMapOf (Y : Scheme) (hom : Y ⟶ Spec (CommRingCat.of R)) :
    R →+* Scheme.Γ.obj (Opposite.op Y) :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ Scheme.Γ.map hom.op).hom

noncomputable def gammaAlgebraOf (Y : Scheme)
    (hom : Y ⟶ Spec (CommRingCat.of R)) :
    Algebra R (Scheme.Γ.obj (Opposite.op Y)) :=
  (gammaAlgebraMapOf Y hom).toAlgebra

theorem gammaBridgeOf (Y : Scheme) [IsAffine Y]
    (hom : Y ⟶ Spec (CommRingCat.of R)) :
    Y.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (gammaAlgebraMapOf Y hom)) = hom := by
  have hnat := Scheme.isoSpec_hom_naturality (X := Y)
    (Y := Spec (CommRingCat.of R)) hom
  rw [Scheme.isoSpec_Spec_hom] at hnat
  have hcomp : (Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫
      CommRingCat.ofHom (gammaAlgebraMapOf Y hom) = Scheme.Γ.map hom.op := by
    rw [show CommRingCat.ofHom (gammaAlgebraMapOf Y hom) =
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ Scheme.Γ.map hom.op from rfl]
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  have happ : hom.appTop = Scheme.Γ.map hom.op := rfl
  have hcomp' := congrArg Spec.map hcomp
  erw [Spec.map_comp] at hcomp'
  rw [← happ] at hcomp'
  have hmap : Spec.map hom.appTop =
      Spec.map (CommRingCat.ofHom (gammaAlgebraMapOf Y hom)) ≫
        Spec.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom := hcomp'.symm
  rw [hmap] at hnat
  refine (cancel_mono (Spec.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom)).mp ?_
  change (Y.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (gammaAlgebraMapOf Y hom))) ≫
      Spec.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom =
    hom ≫ Spec.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom
  exact hnat

theorem gammaSpecMapEqOf (Y : Scheme) [IsAffine Y]
    (hom : Y ⟶ Spec (CommRingCat.of R)) :
    Spec.map (CommRingCat.ofHom (gammaAlgebraMapOf Y hom)) =
      Y.isoSpec.inv ≫ hom := by
  conv_rhs => rw [← gammaBridgeOf Y hom]
  rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  rfl

theorem gammaEtaleOf (Y : Scheme) [IsAffine Y]
    (hom : Y ⟶ Spec (CommRingCat.of R)) (h : Etale hom)
    [Algebra R (Scheme.Γ.obj (Opposite.op Y))]
    (halg : algebraMap R (Scheme.Γ.obj (Opposite.op Y)) =
      gammaAlgebraMapOf Y hom) :
    Algebra.Etale R (Scheme.Γ.obj (Opposite.op Y)) := by
  have hspec := gammaSpecMapEqOf Y hom
  have het : Etale (Spec.map (CommRingCat.ofHom (gammaAlgebraMapOf Y hom))) := by
    rw [hspec]
    exact (MorphismProperty.cancel_left_of_respectsIso (P := @Etale)
      Y.isoSpec.inv hom).mpr h
  have hEt : (CommRingCat.Hom.hom (CommRingCat.ofHom (gammaAlgebraMapOf Y hom))).Etale :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mp het
  rw [← halg] at hEt
  exact (RingHom.etale_algebraMap (R := R)
    (S := Scheme.Γ.obj (Opposite.op Y))).mp hEt

theorem gammaFiniteOf (Y : Scheme) [IsAffine Y]
    (hom : Y ⟶ Spec (CommRingCat.of R)) (h : IsFinite hom)
    [Algebra R (Scheme.Γ.obj (Opposite.op Y))]
    (halg : algebraMap R (Scheme.Γ.obj (Opposite.op Y)) =
      gammaAlgebraMapOf Y hom) :
    Module.Finite R (Scheme.Γ.obj (Opposite.op Y)) := by
  have hspec := gammaSpecMapEqOf Y hom
  have hfin : IsFinite (Spec.map (CommRingCat.ofHom (gammaAlgebraMapOf Y hom))) := by
    rw [hspec]
    exact (MorphismProperty.cancel_left_of_respectsIso (P := @IsFinite)
      Y.isoSpec.inv hom).mpr h
  have hFin : (CommRingCat.Hom.hom (CommRingCat.ofHom (gammaAlgebraMapOf Y hom))).Finite :=
    (AlgebraicGeometry.IsFinite.SpecMap_iff
      (CommRingCat.ofHom (gammaAlgebraMapOf Y hom))).mp hfin
  rw [← halg] at hFin
  exact (RingHom.finite_algebraMap (A := R)
    (B := Scheme.Γ.obj (Opposite.op Y))).mp hFin

#check gammaAlgebraMapOf
#check gammaBridgeOf
#check gammaEtaleOf
#check gammaFiniteOf
end LeanFormal.IUT.XiFPaper.S3127GammaRAlgebraActual
end
