import tmp.sheaf.xif.paper.S1799AffineFiniteEtaleEquivActual

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

namespace LeanFormal.IUT.XiFPaper.S1799AffineFiniteEtaleEquivActual

universe u

variable (R : Type u) [CommRing R]

attribute [instance] sectionsAlgebra

/-! ## 5. The backward functor: a cover maps to its R-algebra of global sections -/

/-- The canonical isomorphism of covers, as a compatibility of structure maps. -/
theorem coverSections_iso_hom_comp (C : FiniteEtaleCover (specBase R)) :
    (Scheme.isoSpec C.carrier).hom ≫ (coverSectionsCover R C).structureMap = C.structureMap := by
  let A := coverSections R C
  letI : Algebra R A := sectionsAlgebra R C
  let hl : C.carrier ≅ Spec (CommRingCat.of A) := Scheme.isoSpec C.carrier
  have hmap : (coverSectionsCover R C).structureMap =
      Spec.map (CommRingCat.ofHom (algebraMap R A)) := rfl
  rw [hmap]
  have halg : (CommRingCat.ofHom (algebraMap R A)) =
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ C.structureMap.appTop := by
    rw [show algebraMap R A = sectionsAlgebraMap R C from rfl]
    rfl
  rw [halg, Spec.map_comp]
  rw [← Category.assoc, Scheme.isoSpec_hom_naturality C.structureMap, Category.assoc]
  rw [show (Spec (CommRingCat.of R)).isoSpec.hom =
      Spec.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom from Scheme.isoSpec_Spec_hom _]
  rw [← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]

/-- The inverse direction: the canonical map from Spec of the global sections to X
is a morphism of covers. -/
theorem coverSections_iso_inv_comp (C : FiniteEtaleCover (specBase R)) :
    (Scheme.isoSpec C.carrier).inv ≫ C.structureMap = (coverSectionsCover R C).structureMap := by
  rw [← coverSections_iso_hom_comp R C, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/- The R-algebra structure map on global sections is natural. -/
theorem sectionsAlgebraMap_natural {C D : FiniteEtaleCover (specBase R)} (φ : C ⟶ D) (r : R) :
    φ.hom.left.appTop.hom (sectionsAlgebraMap R D r) = sectionsAlgebraMap R C r := by
  have h := congrArg
    (fun (g : C.carrier ⟶ specBase R) => g.appTop.hom ((sectionsOfSpecEquiv R).symm r))
    φ.hom.w
  simp only [FiniteEtaleCover.structureMap, Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
    RingHom.coe_comp, Function.comp_apply, sectionsAlgebraMap] at h ⊢
  exact h

/-- The algebra map on global sections induced by a morphism of covers. -/
noncomputable def sectionsAlgHom {C D : FiniteEtaleCover (specBase R)} (φ : C ⟶ D) :
    (coverSectionsFiniteEtale R D).obj →ₐ[R] (coverSectionsFiniteEtale R C).obj where
  toRingHom := φ.hom.left.appTop.hom
  commutes' := sectionsAlgebraMap_natural R φ

/-! ## 6. The functor "cover maps to global sections" -/

/-- The functor from finite etale covers of Spec R to finite etale R-algebras
sending a cover to its R-algebra of global sections. -/
noncomputable def coverToAlg :
    FiniteEtaleCover (specBase R) ⥤ (CommAlgCat.FiniteEtale.{u} R)ᵒᵖ where
  obj C := Opposite.op (coverSectionsFiniteEtale R C)
  map {C D} φ := Opposite.op (ObjectProperty.homMk (CommAlgCat.ofHom (sectionsAlgHom R φ)))
  map_id C := by
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    rfl
  map_comp {C D E} φ ψ := by
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    rfl

@[simp] theorem coverToAlg_obj (C : FiniteEtaleCover (specBase R)) :
    (coverToAlg R).obj C = Opposite.op (coverSectionsFiniteEtale R C) := rfl

/-! ## 7. The unit comparison: global sections of the cover of A are A -/

/-- The unit of the comparison on objects: the global sections of Spec A are A. -/
noncomputable def sectionsAlgEquiv (A : CommAlgCat.FiniteEtale.{u} R) :
    (coverSectionsFiniteEtale R (finiteEtaleAlgebraCover R A)).obj ≃ₐ[R] A.obj :=
  AlgEquiv.ofRingEquiv
    (f := (Scheme.ΓSpecIso (CommRingCat.of A.obj)).commRingCatIsoToRingEquiv) (by
      intro r
      have hnat := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R A.obj))
      have h := congrArg
        (fun (g : Γ(Spec (CommRingCat.of R), ⊤) ⟶ CommRingCat.of A.obj) =>
          g.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)) hnat
      simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h
      rw [Iso.inv_hom_id_apply] at h
      exact h)

/-- The unit of the comparison, componentwise. -/
noncomputable def unitApp (A : (CommAlgCat.FiniteEtale.{u} R)ᵒᵖ) :
    A ≅ (algToCover R ⋙ coverToAlg R).obj A :=
  Iso.op (CommAlgCat.FiniteEtale.isoMk (sectionsAlgEquiv R A.unop))

/-- Essential surjectivity of the global-sections functor. -/
theorem coverToAlg_essSurj : (coverToAlg R).EssSurj :=
  ⟨fun A => ⟨(algToCover R).obj A, ⟨(unitApp R A).symm⟩⟩⟩

/-! ## 8. The counit: Spec of the global sections of C is C -/

/-- The counit of the comparison, componentwise: the canonical isomorphism
from Spec of the global sections of C to C, as a morphism of covers. -/
noncomputable def counitApp (C : FiniteEtaleCover (specBase R)) :
    (coverToAlg R ⋙ algToCover R).obj C ≅ C :=
  ObjectProperty.isoMk (P := fun X : Over (specBase R) => IsFiniteEtaleHom X.hom)
    (Over.isoMk (@Scheme.isoSpec C.carrier (finiteEtaleCoverCarrierIsAffine R C)).symm
      (coverSections_iso_inv_comp R C))

/-- The underlying scheme morphism of the counit. -/
theorem counitApp_hom_left (C : FiniteEtaleCover (specBase R)) :
    (counitApp R C).hom.hom.left = (Scheme.isoSpec C.carrier).inv := rfl

/-- The value of the composite functor on a morphism of covers. -/
theorem comp_map_left {C D : FiniteEtaleCover (specBase R)} (φ : C ⟶ D) :
    ((coverToAlg R ⋙ algToCover R).map φ).hom.left =
      Spec.map (CommRingCat.ofHom (sectionsAlgHom R φ).toRingHom) := rfl

/-- The counit comparison is natural. -/
theorem counitApp_naturality {C D : FiniteEtaleCover (specBase R)} (φ : C ⟶ D) :
    (coverToAlg R ⋙ algToCover R).map φ ≫ (counitApp R D).hom =
      (counitApp R C).hom ≫ (𝟭 (FiniteEtaleCover (specBase R))).map φ := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  simp only [Functor.comp_map, Functor.id_map]
  exact @Scheme.isoSpec_inv_naturality C.carrier D.carrier
    (finiteEtaleCoverCarrierIsAffine R C) (finiteEtaleCoverCarrierIsAffine R D) φ.hom.left

/-- The counit of the comparison. -/
noncomputable def counitIso :
    coverToAlg R ⋙ algToCover R ≅ 𝟭 (FiniteEtaleCover (specBase R)) :=
  NatIso.ofComponents (fun C => counitApp R C) (fun {C D} φ => counitApp_naturality R φ)

/-- Faithfulness of the global-sections functor, from the counit and faithfulness
of the Spec functor. -/
instance coverToAlg_faithful : (coverToAlg R).Faithful :=
  Functor.Faithful.of_comp_iso (counitIso R)

/-- Fullness of the global-sections functor, from the counit, fullness of the
identity and faithfulness of the Spec functor. -/
instance coverToAlg_full : (coverToAlg R).Full :=
  Functor.Full.of_comp_faithful_iso (counitIso R)

/-- The global-sections functor is an equivalence of categories. -/
instance coverToAlg_isEquivalence : (coverToAlg R).IsEquivalence where
  faithful := inferInstance
  full := inferInstance
  essSurj := coverToAlg_essSurj R

/-- The affine finite-etale comparison, in the cover-first direction. -/
noncomputable def affineFiniteEtaleEquivalenceCoverFirst :
    FiniteEtaleCover (specBase R) ≌ (CommAlgCat.FiniteEtale.{u} R)ᵒᵖ :=
  (coverToAlg R).asEquivalence


/-- Unit comparison, elementwise. -/
theorem unitApp_hom_unop_apply (A : (CommAlgCat.FiniteEtale.{u} R)ᵒᵖ)
    (y : ↑(Opposite.unop ((algToCover R ⋙ coverToAlg R).obj A)).obj) :
    (CommAlgCat.Hom.hom (unitApp R A).hom.unop.hom) y =
      (Scheme.ΓSpecIso (CommRingCat.of (A.unop).obj)).hom.hom y := rfl

/-- The global-sections functor on morphisms, elementwise. -/
theorem coverToAlg_map_apply {C D : FiniteEtaleCover (specBase R)} (φ : C ⟶ D)
    (y : (coverSectionsFiniteEtale R D).obj) :
    (CommAlgCat.Hom.hom ((coverToAlg R).map φ).unop.hom) y = φ.hom.left.appTop.hom y :=
  rfl

/-- The Spec functor on morphisms, on underlying schemes. -/
theorem algToCover_map_left {A B : (CommAlgCat.FiniteEtale.{u} R)ᵒᵖ} (f : A ⟶ B) :
    ((algToCover R).map f).hom.left =
      Spec.map (CommRingCat.ofHom (f.unop.hom.hom.toRingHom)) :=
  rfl

/-- The unit comparison is natural. -/
theorem unitApp_naturality {A B : (CommAlgCat.FiniteEtale.{u} R)ᵒᵖ} (f : A ⟶ B) :
    (𝟭 (CommAlgCat.FiniteEtale.{u} R)ᵒᵖ).map f ≫ (unitApp R B).hom =
      (unitApp R A).hom ≫ (algToCover R ⋙ coverToAlg R).map f := by
  apply Quiver.Hom.unop_inj
  apply ObjectProperty.hom_ext
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro x
  simp
  simp only [AlgHom.comp_apply, RingHom.comp_apply]
  rw [unitApp_hom_unop_apply R B x, coverToAlg_map_apply R ((algToCover R).map f) x]
  have hnat := congrFun (congrArg CommRingCat.Hom.hom
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (f.unop.hom.hom.toRingHom)))) x
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at hnat
  exact hnat.symm
end LeanFormal.IUT.XiFPaper.S1799AffineFiniteEtaleEquivActual