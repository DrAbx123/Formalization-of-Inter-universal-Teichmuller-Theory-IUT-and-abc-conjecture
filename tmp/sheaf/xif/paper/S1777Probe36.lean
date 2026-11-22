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
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual

namespace Probe36

abbrev R : Type := S1726CoordinateRing
abbrev Base : Scheme.{0} := S1726AffineScheme
abbrev Alg : Type 1 := CommAlgCat.FiniteEtale.{0} R

noncomputable def structMap (A : CommAlgCat.FiniteEtale.{0} R) :
    Spec (CommRingCat.of (↥A)) ⟶ Base :=
  Spec.map (CommRingCat.ofHom (algebraMap R (↥A)))

lemma structMap_isFinite (A : CommAlgCat.FiniteEtale.{0} R) : IsFinite (structMap A) := by
  rw [structMap, IsFinite.SpecMap_iff, CommRingCat.hom_ofHom]
  exact RingHom.finite_algebraMap.mpr inferInstance

lemma structMap_etale (A : CommAlgCat.FiniteEtale.{0} R) : Etale (structMap A) := by
  rw [structMap, HasRingHomProperty.Spec_iff (P := @Etale) (Q := @RingHom.Etale),
    CommRingCat.hom_ofHom]
  exact RingHom.etale_algebraMap.mpr inferInstance

noncomputable def obj (A : Algᵒᵖ) : S1733Slice :=
  MorphismProperty.CostructuredArrow.mk (Q := ⊤) (P := S1733FiniteEtale)
    (F := Scheme.Spec) (X := Base) (structMap A.unop)
    ⟨structMap_isFinite A.unop, structMap_etale A.unop⟩

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
    rw [← Spec.map_comp, Iso.inv_hom_id, Spec.map_id]
  rw [algMap, Spec.map_comp, Spec.map_comp, ← h, Category.assoc, hominv, Category.comp_id]

lemma appTop_finite (X : S1733Slice) : RingHom.Finite (X.hom.appTop).hom := by
  haveI : IsAffine ((Functor.fromPUnit S1733BaseScheme).obj X.right) :=
    inferInstanceAs (IsAffine S1733BaseScheme)
  exact (X.prop.1).finite_app ⊤ (isAffineOpen_top _)

lemma appTop_etale (X : S1733Slice) : RingHom.Etale (X.hom.appTop).hom := by
  haveI : IsAffine ((Functor.fromPUnit S1733BaseScheme).obj X.right) :=
    inferInstanceAs (IsAffine S1733BaseScheme)
  have h := (X.prop.2).etale_appLE (U := ⊤) (isAffineOpen_top _) (V := ⊤)
    (isAffineOpen_top _) le_top
  exact h

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

noncomputable def sliceAlgebra (X : S1733Slice) : Algᵒᵖ :=
  letI : Algebra R (↥X.left.unop) := (algMap X).hom.toAlgebra
  letI : Module.Finite R (↥X.left.unop) := by
    rw [← RingHom.finite_algebraMap, RingHom.algebraMap_toAlgebra]
    exact algMap_finite X
  letI : Algebra.Etale R (↥X.left.unop) := by
    rw [← RingHom.etale_algebraMap, RingHom.algebraMap_toAlgebra]
    exact algMap_etale X
  Opposite.op (CommAlgCat.FiniteEtale.of R (↥X.left.unop))

lemma sliceAlgebra_algebraMap (X : S1733Slice) :
    algebraMap R (↥(sliceAlgebra X).unop) = (algMap X).hom := by
  show algebraMap R (↥X.left.unop) = (algMap X).hom
  exact RingHom.algebraMap_toAlgebra (algMap X).hom

end Probe36
