import tmp.sheaf.xif.paper.S1733EssentiallySmallCoversActual
import Mathlib.RingTheory.Etale.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.AffineScheme

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace S1815Probe1

open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual

abbrev R : Type := S1726CoordinateRing
abbrev Base : Scheme.{0} := S1733BaseScheme
abbrev Alg : Type 1 := CommAlgCat.FiniteEtale.{0} R

noncomputable def structMap (A : Alg) : Spec (CommRingCat.of (↥A)) ⟶ Base :=
  Spec.map (CommRingCat.ofHom (algebraMap R (↥A)))

lemma structMap_isFinite (A : Alg) : IsFinite (structMap A) := by
  rw [structMap, IsFinite.SpecMap_iff, CommRingCat.hom_ofHom]
  exact RingHom.finite_algebraMap.mpr inferInstance

lemma structMap_etale (A : Alg) : Etale (structMap A) := by
  rw [structMap, HasRingHomProperty.Spec_iff (P := @Etale) (Q := @RingHom.Etale),
    CommRingCat.hom_ofHom]
  exact RingHom.etale_algebraMap.mpr inferInstance

noncomputable def obj (A : Algᵒᵖ) : S1733Slice :=
  MorphismProperty.CostructuredArrow.mk (Q := ⊤) (P := S1733FiniteEtale)
    (F := Scheme.Spec) (X := Base) (structMap A.unop)
    ⟨structMap_isFinite A.unop, structMap_etale A.unop⟩

@[simp] lemma obj_left (A : Algᵒᵖ) :
    (obj A).left = Opposite.op (CommRingCat.of (↥A.unop)) := rfl
@[simp] lemma obj_hom (A : Algᵒᵖ) : (obj A).hom = structMap A.unop := rfl

lemma structMap_comp {A B : Algᵒᵖ} (g : A ⟶ B) :
    CommRingCat.ofHom (algebraMap R (↥B.unop)) ≫
        CommRingCat.ofHom g.unop.hom.hom.toRingHom =
      CommRingCat.ofHom (algebraMap R (↥A.unop)) := by
  rw [← CommRingCat.ofHom_comp]
  apply congrArg CommRingCat.ofHom
  apply RingHom.ext
  intro x
  exact g.unop.hom.hom.commutes x

lemma sliceFunctor_map_triangle {A B : Algᵒᵖ} (g : A ⟶ B) :
    Scheme.Spec.map
        (Opposite.op (CommRingCat.ofHom g.unop.hom.hom.toRingHom)) ≫ structMap B.unop =
      structMap A.unop := by
  show Spec.map (CommRingCat.ofHom g.unop.hom.hom.toRingHom) ≫ structMap B.unop = structMap A.unop
  rw [structMap, structMap, ← Spec.map_comp]
  exact congrArg Spec.map (structMap_comp g)

noncomputable def sliceFunctor : Algᵒᵖ ⥤ S1733Slice where
  obj := obj
  map {A B} g :=
    MorphismProperty.CostructuredArrow.homMk (Q := ⊤) (P := S1733FiniteEtale)
      (F := Scheme.Spec) (X := Base)
      (Opposite.op (CommRingCat.ofHom g.unop.hom.hom.toRingHom)) (by trivial)
      (sliceFunctor_map_triangle g)
  map_id A := by
    apply MorphismProperty.CostructuredArrow.Hom.ext
    show (Opposite.op (CommRingCat.ofHom (𝟙 A).unop.hom.hom.toRingHom) : _) =
      𝟙 (Opposite.op (CommRingCat.of (↥A.unop)))
    rw [show (𝟙 A).unop.hom.hom.toRingHom = RingHom.id (↥A.unop) from rfl, CommRingCat.ofHom_id]
    exact CategoryTheory.op_id
  map_comp {A B C} g h := by
    apply MorphismProperty.CostructuredArrow.Hom.ext
    rfl


lemma sliceHom_algMap_comp {A B : Algᵒᵖ} (φ : obj A ⟶ obj B) :
    CommRingCat.ofHom (algebraMap R (↥B.unop)) ≫ φ.left.unop =
      CommRingCat.ofHom (algebraMap R (↥A.unop)) := by
  have htri : Scheme.Spec.map φ.left ≫ (obj B).hom = (obj A).hom := φ.w
  have hgoal : Spec.map (CommRingCat.ofHom (algebraMap R (↥B.unop)) ≫ φ.left.unop) =
      Spec.map (CommRingCat.ofHom (algebraMap R (↥A.unop))) := by
    rw [Spec.map_comp]
    exact htri
  exact Spec.map_injective hgoal

instance sliceFunctor_faithful : sliceFunctor.Faithful where
  map_injective {A B} f g h := by
    have hleft : (sliceFunctor.map f).left = (sliceFunctor.map g).left :=
      congrArg (fun φ => φ.left) h
    have h1 : (CommRingCat.ofHom f.unop.hom.hom.toRingHom) =
        (CommRingCat.ofHom g.unop.hom.hom.toRingHom) := Quiver.Hom.op_inj hleft
    have h2 : f.unop.hom.hom.toRingHom = g.unop.hom.hom.toRingHom :=
      congrArg CommRingCat.Hom.hom h1
    have h3 : f.unop.hom.hom = g.unop.hom.hom :=
      AlgHom.ext (fun x => congrArg (fun φ => φ x) h2)
    have h4 : f.unop.hom = g.unop.hom := CommAlgCat.hom_ext h3
    have h5 : f.unop = g.unop := InducedCategory.hom_ext h4
    exact Opposite.unop_injective h5

instance sliceFunctor_full : sliceFunctor.Full where
  map_surjective {A B} φ := by
    have hcomm : CommRingCat.ofHom (algebraMap R (↥B.unop)) ≫ φ.left.unop =
        CommRingCat.ofHom (algebraMap R (↥A.unop)) := sliceHom_algMap_comp φ
    let ψ : ↥(B.unop) →ₐ[R] ↥(A.unop) :=
      { toRingHom := CommRingCat.Hom.hom φ.left.unop
        commutes' := fun x => by
          have h := congrArg (fun (f : CommRingCat.of R ⟶ CommRingCat.of (↥A.unop)) =>
            (CommRingCat.Hom.hom f) x) hcomm
          change (CommRingCat.Hom.hom φ.left.unop) (algebraMap R (↥B.unop) x) =
            algebraMap R (↥A.unop) x at h
          exact h }
    let ghom : B.unop ⟶ A.unop := InducedCategory.homMk (CommAlgCat.ofHom ψ)
    refine ⟨ghom.op, ?_⟩
    apply MorphismProperty.CostructuredArrow.Hom.ext
    show (Opposite.op (CommRingCat.ofHom (CommRingCat.Hom.hom φ.left.unop)) : _) = φ.left
    rw [CommRingCat.ofHom_hom]
    exact Quiver.Hom.op_unop φ.left


/-- The R'-algebra structure on the coordinate ring of a slice object:
the unique ring map whose Spec is the structure morphism. -/
noncomputable def algMap (X : S1733Slice) : CommRingCat.of R ⟶ X.left.unop :=
  Spec.preimage X.hom

lemma Spec_map_algMap (X : S1733Slice) :
    Spec.map (algMap X) = X.hom :=
  Spec.map_preimage X.hom

lemma algMap_finite (X : S1733Slice) : RingHom.Finite (algMap X).hom := by
  have h : IsFinite (Spec.map (algMap X)) := by
    rw [Spec_map_algMap]
    exact X.prop.1
  exact (IsFinite.SpecMap_iff (f := algMap X)).mp h

lemma algMap_etale (X : S1733Slice) : RingHom.Etale (algMap X).hom := by
  have h : Etale (Spec.map (algMap X)) := by
    rw [Spec_map_algMap]
    exact X.prop.2
  exact (HasRingHomProperty.Spec_iff (P := @Etale) (Q := @RingHom.Etale)
    (φ := algMap X)).mp h

/-- The finite etale R'-algebra attached to a slice object. -/
noncomputable def sliceAlg (X : S1733Slice) : Alg :=
  letI : Algebra R (↥X.left.unop) := (algMap X).hom.toAlgebra
  letI : Module.Finite R (↥X.left.unop) :=
    RingHom.finite_algebraMap.mpr (algMap_finite X)
  letI : Algebra.Etale R (↥X.left.unop) :=
    RingHom.etale_algebraMap.mp (algMap_etale X)
  CommAlgCat.FiniteEtale.of R (↥X.left.unop)

/-- The slice object is isomorphic to the algebra object. -/
noncomputable def sliceIso (X : S1733Slice) : obj (Opposite.op (sliceAlg X)) ≅ X := by
  classical
  letI : Algebra R (↥X.left.unop) := (algMap X).hom.toAlgebra
  letI : Module.Finite R (↥X.left.unop) :=
    RingHom.finite_algebraMap.mpr (algMap_finite X)
  letI : Algebra.Etale R (↥X.left.unop) :=
    RingHom.etale_algebraMap.mp (algMap_etale X)
  refine MorphismProperty.CostructuredArrow.isoMk (Q := ⊤) (P := S1733FiniteEtale)
    (F := Scheme.Spec) (X := Base) (Iso.refl X.left) (by trivial) (by trivial) ?_
  change Scheme.Spec.map (Iso.refl X.left).hom ≫ X.hom = (obj (Opposite.op (sliceAlg X))).hom
  rw [Iso.refl_hom, Scheme.Spec.map_id, Category.id_comp]
  exact (Spec_map_algMap X).symm

theorem sliceFunctor_essSurj : sliceFunctor.EssSurj :=
  ⟨fun X => ⟨Opposite.op (sliceAlg X), ⟨sliceIso X⟩⟩⟩

instance sliceFunctor_isEquivalence : sliceFunctor.IsEquivalence where
  faithful := sliceFunctor_faithful
  full := sliceFunctor_full
  essSurj := sliceFunctor_essSurj

/-- The affine finite-etale slice is equivalent to the opposite finite etale
algebra category. -/
noncomputable def sliceEquivalence : Algᵒᵖ ≌ S1733Slice :=
  sliceFunctor.asEquivalence

end S1815Probe1