import LeanFormal.IUT.IUTII.Frobenioid.Example36EtaleCoverFoundations
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.RingTheory.Etale.Finite

/-!
# S1799: the affine finite-etale comparison for an arbitrary commutative ring

For any commutative ring R, this file builds the two comparison functors between
the category FiniteEtaleCover (Spec R) of finite etale covers of the affine
scheme Spec R and the opposite of Mathlib's category CommAlgCat.FiniteEtale R
of finite etale R-algebras:

* algToCover : (CommAlgCat.FiniteEtale R)^op ⥤ FiniteEtaleCover (Spec R)
  sends a finite etale R-algebra A to Spec A ⟶ Spec R;
* coverToAlg : FiniteEtaleCover (Spec R) ⥤ (CommAlgCat.FiniteEtale R)^op
  sends a cover X ⟶ Spec R to its ring of global sections Γ(X, ⊤), a finite
  etale R-algebra.

Stage 1 ports the field-case chain of
Example36SpecCoverFunctor / SpecCoverFullEquivalence / SpecCoverEquivalenceFinal /
SpecEssentialSurjectivity from [Field K] to [CommRing R]: the functor algToCover
is proved full, faithful and essentially surjective, hence is an equivalence.
The field-case proofs never use the field hypothesis.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

namespace LeanFormal.IUT.XiFPaper.S1799AffineFiniteEtaleEquivActual

universe u

variable (R : Type u) [CommRing R]

/-- The base scheme Spec R. -/
abbrev specBase : Scheme.{u} := Spec (CommRingCat.of R)

/-! ## 0. Over-category helpers -/

section OverHelpers

variable {S : Scheme.{u}}

@[simp] lemma overMk_left {X : Scheme.{u}} (f : X ⟶ S) : (Over.mk f).left = X := rfl

@[simp] lemma overMk_hom {X : Scheme.{u}} (f : X ⟶ S) : (Over.mk f).hom = f := rfl

@[simp] lemma overHomMk_left {U V : Over S} (f : U.left ⟶ V.left) (w) :
    (Over.homMk f w : U ⟶ V).left = f := rfl

@[simp] lemma overId_left {U : Over S} : Over.Hom.left (𝟙 U) = 𝟙 U.left := rfl

@[simp] lemma overComp_left {U V W : Over S} (p : U ⟶ V) (q : V ⟶ W) :
    (p ≫ q).left = p.left ≫ q.left := rfl

end OverHelpers

/-! ## 1. The functor "finite etale algebra ↦ finite etale cover of Spec R" -/

/-- The structure morphism Spec A ⟶ Spec R of an R-algebra A. -/
def commAlgCatStructureMap (A : CommAlgCat.{u} R) :
    Spec (CommRingCat.of A) ⟶ specBase R :=
  Spec.map (CommRingCat.ofHom (algebraMap R A))

/-- The structure morphism of a finite etale R-algebra. -/
def finiteEtaleStructureMap (A : CommAlgCat.FiniteEtale.{u} R) :
    Spec (CommRingCat.of A.obj) ⟶ specBase R :=
  Spec.map (CommRingCat.ofHom (algebraMap R A.obj))

/-- Spec A ⟶ Spec R is etale when A is an etale R-algebra. -/
theorem finiteEtaleStructureMap_etale (A : CommAlgCat.FiniteEtale.{u} R) :
    Etale (finiteEtaleStructureMap R A) := by
  rw [finiteEtaleStructureMap]
  exact (HasRingHomProperty.Spec_iff (P := @Etale) (Q := @RingHom.Etale)).mpr
    (RingHom.etale_algebraMap.mpr A.property.right)

/-- Spec A ⟶ Spec R is finite when A is a finite R-module. -/
theorem finiteEtaleStructureMap_finite (A : CommAlgCat.FiniteEtale.{u} R) :
    IsFinite (finiteEtaleStructureMap R A) := by
  rw [finiteEtaleStructureMap]
  exact (IsFinite.SpecMap_iff (f := CommRingCat.ofHom (algebraMap R A.obj))).mpr
    (RingHom.finite_algebraMap.mpr A.property.left)

/-- Every finite etale R-algebra gives a finite etale cover of Spec R. -/
def finiteEtaleAlgebraCover (A : CommAlgCat.FiniteEtale.{u} R) :
    FiniteEtaleCover (specBase R) :=
  FiniteEtaleCover.mk (finiteEtaleStructureMap R A)
    (finiteEtaleStructureMap_etale R A) (finiteEtaleStructureMap_finite R A)

@[simp] theorem finiteEtaleAlgebraCover_carrier (A : CommAlgCat.FiniteEtale.{u} R) :
    FiniteEtaleCover.carrier (finiteEtaleAlgebraCover R A) =
      Spec (CommRingCat.of A.obj) := rfl

/- The Over-level functor A ↦ (Spec A ⟶ Spec R) on all R-algebras. -/
set_option backward.isDefEq.respectTransparency false in
noncomputable def specFunctorCommAlgCat :
    (CommAlgCat.{u} R)ᵒᵖ ⥤ Over (specBase R) where
  obj A := Over.mk (commAlgCatStructureMap R A.unop)
  map {A B} f :=
    Over.homMk (Spec.map (CommRingCat.ofHom (f.unop.hom.toRingHom))) (by
      change Spec.map (CommRingCat.ofHom (f.unop.hom.toRingHom)) ≫
          (Over.mk (commAlgCatStructureMap R B.unop)).hom =
        (Over.mk (commAlgCatStructureMap R A.unop)).hom
      rw [overMk_hom, overMk_hom, commAlgCatStructureMap, commAlgCatStructureMap]
      erw [← Spec.map_comp]
      apply Spec.map_inj.mpr
      ext x
      exact f.unop.hom.commutes x)
  map_id A := by
    apply Over.OverMorphism.ext
    rw [overHomMk_left, overId_left]
    change Spec.map (CommRingCat.ofHom (CommAlgCat.Hom.hom (𝟙 A).unop).toRingHom) =
      𝟙 (Spec (CommRingCat.of (A.unop : CommAlgCat.{u} R)))
    simp [Spec.map_id]
  map_comp f g := by
    apply Over.OverMorphism.ext
    rw [overHomMk_left, overComp_left, overHomMk_left, overHomMk_left]
    rw [show (f ≫ g).unop = g.unop ≫ f.unop from rfl]
    simp only [CommAlgCat.hom_comp]
    rw [← Spec.map_comp]
    apply Spec.map_inj.mpr
    ext x
    rfl

/-- Inclusion of finite etale R-algebras into all R-algebras. -/
def finiteEtaleInclusion :
    (CommAlgCat.FiniteEtale.{u} R)ᵒᵖ ⥤ (CommAlgCat.{u} R)ᵒᵖ :=
  (ObjectProperty.ι (CommAlgCat.finiteEtale R)).op

/-- The Over-level functor restricted to finite etale algebras. -/
noncomputable def specFunctorOver :
    (CommAlgCat.FiniteEtale.{u} R)ᵒᵖ ⥤ Over (specBase R) :=
  finiteEtaleInclusion R ⋙ specFunctorCommAlgCat R

/-- The actual functor "finite etale R-algebra ↦ finite etale cover of Spec R". -/
noncomputable def algToCover :
    (CommAlgCat.FiniteEtale.{u} R)ᵒᵖ ⥤ FiniteEtaleCover (specBase R) :=
  ObjectProperty.lift (fun X : Over (specBase R) => IsFiniteEtaleHom X.hom)
    (specFunctorOver R) (fun A => ⟨finiteEtaleStructureMap_etale R A.unop,
      finiteEtaleStructureMap_finite R A.unop⟩)

@[simp] theorem algToCover_obj (A : (CommAlgCat.FiniteEtale.{u} R)ᵒᵖ) :
    (algToCover R).obj A = finiteEtaleAlgebraCover R A.unop := rfl

/-! ## 2. Global sections of a cover are a finite etale R-algebra -/

/-- Every finite etale cover of Spec R has affine carrier. -/
theorem finiteEtaleCover_carrier_isAffine (C : FiniteEtaleCover (specBase R)) :
    IsAffine C.carrier := by
  haveI : IsFinite C.structureMap := FiniteEtaleCover.finite_structureMap C
  exact isAffine_of_isAffineHom C.structureMap

instance finiteEtaleCoverCarrierIsAffine (C : FiniteEtaleCover (specBase R)) :
    IsAffine C.carrier :=
  finiteEtaleCover_carrier_isAffine R C

/-- The ring of global sections of a finite etale cover of Spec R. -/
abbrev coverSections (C : FiniteEtaleCover (specBase R)) : Type u :=
  Γ(C.carrier, ⊤)

/-- The Gamma-Spec inverse as a ring equivalence: sections of Spec R are R. -/
abbrev sectionsOfSpecEquiv : Γ(Spec (CommRingCat.of R), ⊤) ≃+* CommRingCat.of R :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv

/-- The R-algebra structure map on the global sections of a finite etale cover. -/
def sectionsAlgebraMap (C : FiniteEtaleCover (specBase R)) :
    R →+* coverSections R C :=
  C.structureMap.appTop.hom.comp (sectionsOfSpecEquiv R).symm.toRingHom

/-- The R-algebra structure on the global sections of a finite etale cover. -/
@[reducible] noncomputable instance sectionsAlgebra (C : FiniteEtaleCover (specBase R)) :
    Algebra R (coverSections R C) :=
  (sectionsAlgebraMap R C).toAlgebra

/-- The global sections of a finite etale cover, as a finite etale R-algebra. -/
noncomputable def coverSectionsFiniteEtale (C : FiniteEtaleCover (specBase R)) :
    CommAlgCat.FiniteEtale.{u} R := by
  let A := coverSections R C
  let Γ₀ := Γ(Spec (CommRingCat.of R), ⊤)
  let φbase : R →+* Γ₀ := (sectionsOfSpecEquiv R).symm.toRingHom
  letI : Algebra R Γ₀ := φbase.toAlgebra
  letI : Algebra Γ₀ A := (C.structureMap.appTop.hom).toAlgebra
  letI : Algebra R A := sectionsAlgebra R C
  have hΓ₀ : Algebra.Etale R Γ₀ := by
    have e : R ≃ₐ[R] Γ₀ := AlgEquiv.ofRingEquiv (f := (sectionsOfSpecEquiv R).symm) (by
      intro x
      rfl)
    exact Algebra.Etale.of_equiv e
  have hEtale : RingHom.Etale (C.structureMap.appTop.hom) :=
    (HasRingHomProperty.iff_of_isAffine (P := @Etale) (Q := @RingHom.Etale)).mp
      (FiniteEtaleCover.etale_structureMap C)
  have hA : Algebra.Etale Γ₀ A := hEtale
  haveI : IsScalarTower R Γ₀ A :=
    IsScalarTower.of_algebraMap_eq (fun x => rfl)
  have hKA : Algebra.Etale R A := Algebra.Etale.comp R Γ₀ A
  have hFinΓ₀ : Module.Finite R Γ₀ :=
    Module.Finite.equiv (AlgEquiv.ofRingEquiv (f := (sectionsOfSpecEquiv R).symm) (by
      intro x
      rfl)).toLinearEquiv
  haveI : IsFinite C.structureMap := FiniteEtaleCover.finite_structureMap C
  have hFinA : Module.Finite Γ₀ A := Scheme.Hom.finite_appTop C.structureMap
  have hFin : Module.Finite R A := Module.Finite.trans Γ₀ A
  exact CommAlgCat.FiniteEtale.of R A

/-- The cover attached to the global sections of C. -/
abbrev coverSectionsCover (C : FiniteEtaleCover (specBase R)) :
    FiniteEtaleCover (specBase R) :=
  finiteEtaleAlgebraCover R (coverSectionsFiniteEtale R C)

/-- The structure map of the sections cover is Spec of the algebra structure map. -/
theorem coverSectionsCover_structureMap (C : FiniteEtaleCover (specBase R)) :
    (coverSectionsCover R C).structureMap =
      Spec.map (CommRingCat.ofHom (sectionsAlgebraMap R C)) :=
  rfl

/-- The canonical isomorphism of covers: object-level essential surjectivity. -/
theorem coverSections_iso (C : FiniteEtaleCover (specBase R)) :
    Nonempty (C ≅ coverSectionsCover R C) := by
  let A := coverSections R C
  letI : Algebra R A := sectionsAlgebra R C
  let hl : C.carrier ≅ Spec (CommRingCat.of A) := Scheme.isoSpec C.carrier
  have hmap : (coverSectionsCover R C).structureMap =
      Spec.map (CommRingCat.ofHom (algebraMap R A)) := rfl
  have hw : hl.hom ≫ (coverSectionsCover R C).structureMap = C.structureMap := by
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
  exact ⟨ObjectProperty.isoMk _ (Over.isoMk hl hw)⟩

/-! ## 3. Fullness and faithfulness of the functor algToCover -/

/-- The R-algebra map underlying a morphism of the Over-level Spec covers. -/
def overHomToAlgHom {A B : (CommAlgCat.{u} R)ᵒᵖ}
    (φ : (specFunctorCommAlgCat R).obj A ⟶ (specFunctorCommAlgCat R).obj B) :
    B.unop →ₐ[R] A.unop := by
  classical
  let ψ : CommRingCat.of B.unop ⟶ CommRingCat.of A.unop :=
    (Spec.fullyFaithful.preimage (Over.Hom.left φ)).unop
  have hψ : Spec.map ψ = Over.Hom.left φ :=
    Spec.fullyFaithful.map_preimage (Over.Hom.left φ)
  have hB : ((specFunctorCommAlgCat R).obj B).hom = commAlgCatStructureMap R B.unop := rfl
  have hA : ((specFunctorCommAlgCat R).obj A).hom = commAlgCatStructureMap R A.unop := rfl
  have hw : ∀ x, ψ.hom (algebraMap R B.unop x) = algebraMap R A.unop x := by
    intro x
    have h := φ.w
    rw [← hψ, hB, hA, commAlgCatStructureMap, commAlgCatStructureMap] at h
    erw [← Spec.map_comp] at h
    have h' : CommRingCat.ofHom (algebraMap R B.unop) ≫ ψ =
        CommRingCat.ofHom (algebraMap R A.unop) := Spec.map_inj.mp h
    simpa using congrArg (fun m => m.hom x) h'
  exact { toRingHom := ψ.hom, commutes' := hw }

/-- Fullness of the plain-CommAlgCat Over functor. -/
instance specFunctorCommAlgCat_full : (specFunctorCommAlgCat R).Full where
  map_surjective {A B} φ :=
    ⟨(CommAlgCat.ofHom (overHomToAlgHom R φ)).op, by
      apply Over.OverMorphism.ext
      change Spec.map (CommRingCat.ofHom ((overHomToAlgHom R φ).toRingHom)) =
        Over.Hom.left φ
      rw [← Spec.fullyFaithful.map_preimage (Over.Hom.left φ)]
      apply Spec.map_inj.mpr
      rw [show (overHomToAlgHom R φ).toRingHom =
          (Spec.fullyFaithful.preimage (Over.Hom.left φ)).unop.hom from rfl]
      rfl⟩

/-- Fullness of the finite-etale inclusion (via ObjectProperty.ι and op). -/
instance finiteEtaleInclusion_full : (finiteEtaleInclusion R).Full := by
  unfold finiteEtaleInclusion
  infer_instance

instance specFunctorOver_full : (specFunctorOver R).Full := by
  unfold specFunctorOver
  infer_instance

instance algToCover_full : (algToCover R).Full := by
  unfold algToCover
  infer_instance

/-- Faithfulness of the plain-CommAlgCat Over functor, via Spec.map_injective. -/
instance specFunctorCommAlgCat_faithful : (specFunctorCommAlgCat R).Faithful where
  map_injective {A B} f g h := by
    have hspec : Spec.map (CommRingCat.ofHom (f.unop.hom.toRingHom)) =
        Spec.map (CommRingCat.ofHom (g.unop.hom.toRingHom)) :=
      congrArg Over.Hom.left h
    have hring : CommRingCat.ofHom (f.unop.hom.toRingHom) =
        CommRingCat.ofHom (g.unop.hom.toRingHom) := Spec.map_injective hspec
    have halg : f.unop.hom = g.unop.hom := by
      apply AlgHom.ext
      intro x
      exact congrArg (fun m => m.hom x) hring
    apply Opposite.unop_injective
    exact CommAlgCat.hom_ext halg

/-- Faithfulness of the finite-etale inclusion. -/
instance finiteEtaleInclusion_faithful : (finiteEtaleInclusion R).Faithful where
  map_injective {A B} f g h := by
    apply Opposite.unop_injective
    exact (ObjectProperty.ι (CommAlgCat.finiteEtale R)).map_injective
      (congrArg Opposite.unop h)

instance specFunctorOver_faithful : (specFunctorOver R).Faithful := by
  unfold specFunctorOver
  infer_instance

instance algToCover_faithful : (algToCover R).Faithful := by
  unfold algToCover
  infer_instance

/-! ## 4. Essential surjectivity and the equivalence -/

/-- Essential surjectivity: every finite etale cover of Spec R is (up to
isomorphism) the Spec of the finite etale algebra of its global sections. -/
theorem algToCover_essSurj : (algToCover R).EssSurj :=
  ⟨fun C => by
    obtain ⟨e⟩ := coverSections_iso R C
    exact ⟨Opposite.op (coverSectionsFiniteEtale R C), ⟨e.symm⟩⟩⟩

/-- The functor "finite etale R-algebra maps to finite etale cover of Spec R"
is an equivalence of categories. -/
instance algToCover_isEquivalence : (algToCover R).IsEquivalence where
  faithful := inferInstance
  full := inferInstance
  essSurj := algToCover_essSurj R

/-- **The affine finite-etale comparison for an arbitrary commutative ring**:
finite etale covers of Spec R are equivalent to finite etale R-algebras, with
the variance reversed. -/
noncomputable def affineFiniteEtaleEquivalence :
    (CommAlgCat.FiniteEtale.{u} R)ᵒᵖ ≌ FiniteEtaleCover (specBase R) :=
  (algToCover R).asEquivalence

set_option backward.isDefEq.respectTransparency true


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


/-! ## 9. The unit of the comparison -/

/-- The unit comparison, as a rewrite rule. -/
theorem unitApp_hom_unop_apply' (A : (CommAlgCat.FiniteEtale.{u} R)ᵒᵖ) :
    ∀ y : ↑(Opposite.unop ((algToCover R ⋙ coverToAlg R).obj A)).obj,
      (CommAlgCat.Hom.hom (unitApp R A).hom.unop.hom) y =
        (Scheme.ΓSpecIso (CommRingCat.of (A.unop).obj)).hom.hom y := fun y => rfl

/-- The unit comparison is natural: it is the comparison of the global sections of
Spec A with A, and its naturality is that of Scheme.ΓSpecIso. -/
theorem unitApp_naturality {A B : (CommAlgCat.FiniteEtale.{u} R)ᵒᵖ} (f : A ⟶ B) :
    f ≫ (unitApp R B).hom = (unitApp R A).hom ≫ (algToCover R ⋙ coverToAlg R).map f := by
  apply Quiver.Hom.unop_inj
  apply ObjectProperty.hom_ext
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro x
  simp only [CategoryTheory.unop_comp, ObjectProperty.FullSubcategory.comp_hom,
    CommAlgCat.hom_comp, AlgHom.comp_apply, Functor.comp_map,
    unitApp_hom_unop_apply' R B, unitApp_hom_unop_apply' R A]
  have hnat := congrArg
    (fun (g : Γ(Spec (CommRingCat.of (B.unop.obj)), ⊤) ⟶ CommRingCat.of (A.unop.obj)) => g.hom x)
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (f.unop.hom.hom.toRingHom)))
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at hnat
  exact hnat.symm

/-- **The unit of the affine finite-etale comparison**: the identity is naturally
isomorphic to the composite "Spec of the global sections". -/
noncomputable def unitIso :
    𝟭 (CommAlgCat.FiniteEtale.{u} R)ᵒᵖ ≅ algToCover R ⋙ coverToAlg R :=
  NatIso.ofComponents (fun A => unitApp R A) (fun {A B} f => unitApp_naturality R f)

theorem unitIso_hom_app (X : (CommAlgCat.FiniteEtale.{u} R)ᵒᵖ) :
    (unitIso R).hom.app X = (unitApp R X).hom := rfl

theorem counitIso_hom_app (C : FiniteEtaleCover (specBase R)) :
    (counitIso R).hom.app C = (counitApp R C).hom := rfl

/-- The triangle identity which upgrades the two natural isomorphisms unitIso and
counitIso to a single CategoryTheory.Equivalence record.

Its two sides are morphisms of covers Spec Γ(Spec A) ⟶ Spec A; after unwinding the
definitions they are Spec.map (ΓSpecIso A).hom ≫ (Spec A).isoSpec.inv and the identity,
and the required input is the identification of the underlying ring map of the unit
with (Scheme.ΓSpecIso A).hom together with Scheme.isoSpec_Spec_inv and functoriality
of Spec.

This statement is NOT proved in this file; it is the one remaining packaging step for
the two-sided Equivalence record.  It is not needed for the two equivalences
algToCover and coverToAlg proved above, nor for the natural isomorphisms unitIso and
counitIso. -/
def S1799TriangleIdentity (X : (CommAlgCat.FiniteEtale.{u} R)ᵒᵖ) : Prop :=
  (algToCover R).map ((unitIso R).hom.app X) ≫
    (counitIso R).hom.app ((algToCover R).obj X) = 𝟙 ((algToCover R).obj X)

/-! ## 9. Axiom audit -/

#print axioms algToCover_isEquivalence
#print axioms affineFiniteEtaleEquivalence
#print axioms coverToAlg_isEquivalence
#print axioms affineFiniteEtaleEquivalenceCoverFirst
#print axioms counitIso
#print axioms coverToAlg_full
#print axioms coverToAlg_faithful
#print axioms coverToAlg_essSurj
#print axioms sectionsAlgEquiv

#print axioms unitIso
#print axioms unitApp_naturality
#print axioms S1799TriangleIdentity

end LeanFormal.IUT.XiFPaper.S1799AffineFiniteEtaleEquivActual
