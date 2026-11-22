import tmp.sheaf.xif.paper.S1743CoverSliceActual
import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.RingHom.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.AffineScheme

noncomputable section
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual

namespace Probe32

abbrev R : Type := S1726CoordinateRing
abbrev Base : Scheme.{0} := S1726AffineScheme
abbrev Alg : Type 1 := CommAlgCat.FiniteEtale.{0} R

/-- The algebra map R' -> global sections of the affine model. -/
noncomputable def algMap (X : S1733Slice) : CommRingCat.of R ⟶ X.left.unop :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ X.hom.appTop ≫ (Scheme.ΓSpecIso X.left.unop).hom

theorem Spec_map_algMap (X : S1733Slice) : Spec.map (algMap X) = X.hom := by
  have h0 := Scheme.isoSpec_hom_naturality X.hom
  have h : (Spec X.left.unop).isoSpec.hom ≫ Spec.map X.hom.appTop =
      X.hom ≫ (Spec (CommRingCat.of R)).isoSpec.hom := h0
  rw [Scheme.isoSpec_Spec_hom, Scheme.isoSpec_Spec_hom] at h
  rw [← Spec.map_comp] at h
  have hominv : Spec.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫
      Spec.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv = 𝟙 (Spec (CommRingCat.of R)) := by
    rw [← Spec.map_comp, Iso.hom_inv_id, Spec.map_id]
  rw [algMap, Category.assoc, Spec.map_comp, Spec.map_comp]
  rw [show Spec.map (Scheme.ΓSpecIso X.left.unop).hom ≫ Spec.map X.hom.appTop =
      X.hom ≫ Spec.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom from h]
  rw [Category.assoc, hominv, Category.comp_id]

lemma appTop_finite (X : S1733Slice) : RingHom.Finite (X.hom.appTop).hom := by
  haveI : IsAffine ((Functor.fromPUnit S1733BaseScheme).obj X.right) := by
    show IsAffine S1733BaseScheme
    infer_instance
  have h : IsFinite X.hom := X.prop.1
  exact ((HasAffineProperty.iff_of_isAffine (P := @IsFinite) (f := X.hom)).mp h).2

lemma appTop_etale (X : S1733Slice) : RingHom.Etale (X.hom.appTop).hom := by
  haveI : IsAffine ((Functor.fromPUnit S1733BaseScheme).obj X.right) := by
    show IsAffine S1733BaseScheme
    infer_instance
  have h : Etale X.hom := X.prop.2
  exact (HasRingHomProperty.iff_of_isAffine (P := @Etale) (Q := @RingHom.Etale)
    (f := X.hom)).mp h

lemma finite_of_iso_commRingCat {A B : CommRingCat} (f : A ⟶ B) [IsIso f] :
    RingHom.Finite f.hom :=
  RingHom.Finite.of_surjective f.hom
    ((ConcreteCategory.isIso_iff_bijective f).mp inferInstance).2

lemma etale_of_iso_commRingCat {A B : CommRingCat} (f : A ⟶ B) [IsIso f] :
    RingHom.Etale f.hom :=
  RingHom.Etale.of_bijective ((ConcreteCategory.isIso_iff_bijective f).mp inferInstance)

lemma algMap_finite (X : S1733Slice) : RingHom.Finite (algMap X).hom := by
  have h1 : RingHom.Finite (X.hom.appTop).hom := appTop_finite X
  have h2 : RingHom.Finite ((Scheme.ΓSpecIso X.left.unop).hom.hom.comp (X.hom.appTop).hom) :=
    RingHom.Finite.comp (finite_of_iso_commRingCat (Scheme.ΓSpecIso X.left.unop).hom) h1
  have h3 : RingHom.Finite (((Scheme.ΓSpecIso X.left.unop).hom.hom.comp (X.hom.appTop).hom).comp
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) :=
    RingHom.Finite.comp h2 (finite_of_iso_commRingCat (Scheme.ΓSpecIso (CommRingCat.of R)).inv)
  rw [algMap, Category.assoc, CommRingCat.hom_comp, CommRingCat.hom_comp]
  exact h3

lemma algMap_etale (X : S1733Slice) : RingHom.Etale (algMap X).hom := by
  have h1 : RingHom.Etale (X.hom.appTop).hom := appTop_etale X
  have h2 : RingHom.Etale ((Scheme.ΓSpecIso X.left.unop).hom.hom.comp (X.hom.appTop).hom) :=
    RingHom.Etale.stableUnderComposition _ _ h1
      (etale_of_iso_commRingCat (Scheme.ΓSpecIso X.left.unop).hom)
  have h3 : RingHom.Etale (((Scheme.ΓSpecIso X.left.unop).hom.hom.comp (X.hom.appTop).hom).comp
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) :=
    RingHom.Etale.stableUnderComposition _ _ (etale_of_iso_commRingCat
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv) h2
  rw [algMap, Category.assoc, CommRingCat.hom_comp, CommRingCat.hom_comp]
  exact h3

end Probe32
