import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.RingHom.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.AffineScheme

noncomputable section
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry

namespace Gen5

abbrev FE : MorphismProperty Scheme.{0} := @IsFinite ⊓ @Etale
abbrev Base (R : Type) [CommRing R] : Scheme.{0} := Spec (CommRingCat.of R)
abbrev Slice (R : Type) [CommRing R] : Type 1 := FE.CostructuredArrow ⊤ Scheme.Spec (Base R)
abbrev Alg (R : Type) [CommRing R] : Type 1 := CommAlgCat.FiniteEtale.{0} R

variable {R : Type} [CommRing R]

noncomputable def algMap (X : Slice R) : CommRingCat.of R ⟶ X.left.unop :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ X.hom.appTop ≫ (Scheme.ΓSpecIso X.left.unop).hom

theorem Spec_map_algMap (X : Slice R) : Spec.map (algMap X) = X.hom := by
  have h0 := Scheme.isoSpec_hom_naturality X.hom
  have h : (Spec X.left.unop).isoSpec.hom ≫ Spec.map X.hom.appTop =
      X.hom ≫ (Spec (CommRingCat.of R)).isoSpec.hom := h0
  rw [Scheme.isoSpec_Spec_hom, Scheme.isoSpec_Spec_hom] at h
  rw [← Spec.map_comp] at h
  have hominv : Spec.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫
      Spec.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv = 𝟙 (Spec (CommRingCat.of R)) := by
    rw [← Spec.map_comp, Iso.inv_hom_id, Spec.map_id]
  calc Spec.map (algMap X)
      = Spec.map (X.hom.appTop ≫ (Scheme.ΓSpecIso X.left.unop).hom) ≫
          Spec.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv := by
        rw [algMap, Spec.map_comp]
    _ = (X.hom ≫ Spec.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom) ≫
          Spec.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv := by rw [h]
    _ = X.hom := by rw [Category.assoc, hominv, Category.comp_id]

lemma appTop_finite (X : Slice R) : RingHom.Finite (X.hom.appTop).hom := by
  haveI hbase : IsAffine (Base R) := inferInstance
  haveI : IsAffine ((Functor.fromPUnit (Base R)).obj X.right) := hbase
  exact (X.prop.1).finite_app ⊤ (isAffineOpen_top _)

lemma appTop_etale (X : Slice R) : RingHom.Etale (X.hom.appTop).hom := by
  haveI hbase : IsAffine (Base R) := inferInstance
  haveI : IsAffine ((Functor.fromPUnit (Base R)).obj X.right) := hbase
  exact (X.prop.2).etale_appLE (U := ⊤) (isAffineOpen_top _) (V := ⊤) (isAffineOpen_top _) le_top

lemma finite_of_iso {A B : CommRingCat} (f : A ⟶ B) [IsIso f] : RingHom.Finite f.hom :=
  RingHom.Finite.of_surjective f.hom
    ((ConcreteCategory.isIso_iff_bijective f).mp inferInstance).2

lemma etale_of_iso {A B : CommRingCat} (f : A ⟶ B) [IsIso f] : RingHom.Etale f.hom :=
  RingHom.Etale.of_bijective ((ConcreteCategory.isIso_iff_bijective f).mp inferInstance)

lemma algMap_finite (X : Slice R) : RingHom.Finite (algMap X).hom := by
  have h1 : RingHom.Finite (X.hom.appTop).hom := appTop_finite X
  have h2 : RingHom.Finite ((Scheme.ΓSpecIso X.left.unop).hom.hom.comp (X.hom.appTop).hom) :=
    RingHom.Finite.comp (finite_of_iso (Scheme.ΓSpecIso X.left.unop).hom) h1
  have h3 : RingHom.Finite (((Scheme.ΓSpecIso X.left.unop).hom.hom.comp (X.hom.appTop).hom).comp
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) :=
    RingHom.Finite.comp h2 (finite_of_iso (Scheme.ΓSpecIso (CommRingCat.of R)).inv)
  rw [algMap, CommRingCat.hom_comp, CommRingCat.hom_comp]
  exact h3

lemma algMap_etale (X : Slice R) : RingHom.Etale (algMap X).hom := by
  have h1 : RingHom.Etale (X.hom.appTop).hom := appTop_etale X
  have h2 : RingHom.Etale ((Scheme.ΓSpecIso X.left.unop).hom.hom.comp (X.hom.appTop).hom) :=
    RingHom.Etale.stableUnderComposition _ _ h1 (etale_of_iso (Scheme.ΓSpecIso X.left.unop).hom)
  have h3 : RingHom.Etale (((Scheme.ΓSpecIso X.left.unop).hom.hom.comp (X.hom.appTop).hom).comp
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) :=
    RingHom.Etale.stableUnderComposition _ _ (etale_of_iso (Scheme.ΓSpecIso (CommRingCat.of R)).inv) h2
  rw [algMap, CommRingCat.hom_comp, CommRingCat.hom_comp]
  exact h3

noncomputable def sliceAlgebra (X : Slice R) : (Alg R)ᵒᵖ :=
  letI : Algebra R (↥X.left.unop) := (algMap X).hom.toAlgebra
  letI : Module.Finite R (↥X.left.unop) := by
    rw [← RingHom.finite_algebraMap, RingHom.algebraMap_toAlgebra]
    exact algMap_finite X
  letI : Algebra.Etale R (↥X.left.unop) := by
    rw [← RingHom.etale_algebraMap, RingHom.algebraMap_toAlgebra]
    exact algMap_etale X
  Opposite.op (CommAlgCat.FiniteEtale.of R (↥X.left.unop))

lemma sliceAlgebra_algebraMap (X : Slice R) :
    algebraMap R (↥(sliceAlgebra X).unop) = (algMap X).hom := by
  show algebraMap R (↥X.left.unop) = (algMap X).hom
  exact RingHom.algebraMap_toAlgebra (algMap X).hom

end Gen5
