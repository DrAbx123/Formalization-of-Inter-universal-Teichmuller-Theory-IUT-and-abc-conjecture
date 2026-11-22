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

namespace Gen

/-- The finite etale morphism property of schemes. -/
abbrev FE : MorphismProperty Scheme.{0} := @IsFinite ⊓ @Etale

/-- The affine base Spec R. -/
abbrev Base (R : Type) [CommRing R] : Scheme.{0} := Spec (CommRingCat.of R)

/-- The affine finite etale slice over Spec R. -/
abbrev Slice (R : Type) [CommRing R] : Type 1 :=
  FE.CostructuredArrow ⊤ Scheme.Spec (Base R)

/-- Finite etale R-algebras. -/
abbrev Alg (R : Type) [CommRing R] : Type 1 := CommAlgCat.FiniteEtale.{0} R

variable {R : Type} [CommRing R]

example : Category.{0, 1} (Slice R) := inferInstance

/-- The structure morphism Spec A -> Spec R. -/
noncomputable def structMap (A : CommAlgCat.FiniteEtale.{0} R) :
    Spec (CommRingCat.of (↥A)) ⟶ Base R :=
  Spec.map (CommRingCat.ofHom (algebraMap R (↥A)))

lemma structMap_isFinite (A : CommAlgCat.FiniteEtale.{0} R) : IsFinite (structMap A) := by
  rw [structMap, IsFinite.SpecMap_iff, CommRingCat.hom_ofHom]
  exact RingHom.finite_algebraMap.mpr inferInstance

lemma structMap_etale (A : CommAlgCat.FiniteEtale.{0} R) : Etale (structMap A) := by
  rw [structMap, HasRingHomProperty.Spec_iff (P := @Etale) (Q := @RingHom.Etale),
    CommRingCat.hom_ofHom]
  exact RingHom.etale_algebraMap.mpr inferInstance

noncomputable def obj (A : (Alg R)ᵒᵖ) : Slice R :=
  MorphismProperty.CostructuredArrow.mk (Q := ⊤) (P := FE)
    (F := Scheme.Spec) (X := Base R) (structMap A.unop)
    ⟨structMap_isFinite A.unop, structMap_etale A.unop⟩

@[simp] lemma obj_left (A : (Alg R)ᵒᵖ) :
    (obj A).left = Opposite.op (CommRingCat.of (↥A.unop)) := rfl
@[simp] lemma obj_hom (A : (Alg R)ᵒᵖ) : (obj A).hom = structMap A.unop := rfl

lemma structMap_comp {A B : (Alg R)ᵒᵖ} (g : A ⟶ B) :
    CommRingCat.ofHom (algebraMap R (↥B.unop)) ≫
        CommRingCat.ofHom g.unop.hom.hom.toRingHom =
      CommRingCat.ofHom (algebraMap R (↥A.unop)) := by
  rw [← CommRingCat.ofHom_comp]
  apply congrArg CommRingCat.ofHom
  apply RingHom.ext
  intro x
  exact g.unop.hom.hom.commutes x

lemma structMap_triangle {A B : (Alg R)ᵒᵖ} (g : A ⟶ B) :
    Scheme.Spec.map (Opposite.op (CommRingCat.ofHom g.unop.hom.hom.toRingHom)) ≫
        structMap B.unop = structMap A.unop := by
  show Spec.map (CommRingCat.ofHom g.unop.hom.hom.toRingHom) ≫
      structMap B.unop = structMap A.unop
  rw [structMap, structMap, ← Spec.map_comp]
  exact congrArg Spec.map (structMap_comp g)

noncomputable def sliceFunctor : (Alg R)ᵒᵖ ⥤ Slice R where
  obj := obj
  map {A B} g :=
    MorphismProperty.CostructuredArrow.homMk (Q := ⊤) (P := FE)
      (F := Scheme.Spec) (X := Base R)
      (Opposite.op (CommRingCat.ofHom g.unop.hom.hom.toRingHom)) (by trivial)
      (structMap_triangle g)
  map_id A := by
    apply MorphismProperty.CostructuredArrow.Hom.ext
    show (Opposite.op (CommRingCat.ofHom (𝟙 A).unop.hom.hom.toRingHom) : _) =
      𝟙 (Opposite.op (CommRingCat.of (↥A.unop)))
    rw [show (𝟙 A).unop.hom.hom.toRingHom = RingHom.id (↥A.unop) from rfl,
      CommRingCat.ofHom_id]
    exact CategoryTheory.op_id
  map_comp {A B C} g h := by
    apply MorphismProperty.CostructuredArrow.Hom.ext
    rfl

instance sliceFunctor_faithful : (sliceFunctor (R := R)).Faithful where
  map_injective {A B} f g h := by
    have hleft : (sliceFunctor (R := R) |>.map f).left =
        (sliceFunctor (R := R) |>.map g).left :=
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

lemma sliceHom_triangle {A B : (Alg R)ᵒᵖ} (φ : obj A ⟶ obj B) :
    CommRingCat.ofHom (algebraMap R (↥B.unop)) ≫ φ.left.unop =
      CommRingCat.ofHom (algebraMap R (↥A.unop)) := by
  have htri : Scheme.Spec.map φ.left ≫ (obj B).hom = (obj A).hom := φ.w
  have hgoal : Spec.map (CommRingCat.ofHom (algebraMap R (↥B.unop)) ≫ φ.left.unop) =
      Spec.map (CommRingCat.ofHom (algebraMap R (↥A.unop))) := by
    rw [Spec.map_comp]
    exact htri
  exact Spec.map_injective hgoal

instance sliceFunctor_full : (sliceFunctor (R := R)).Full where
  map_surjective {A B} φ := by
    have hcomm : CommRingCat.ofHom (algebraMap R (↥B.unop)) ≫ φ.left.unop =
        CommRingCat.ofHom (algebraMap R (↥A.unop)) := sliceHom_triangle φ
    let g' : ↥(B.unop).obj →+* ↥(A.unop).obj := CommRingCat.Hom.hom φ.left.unop
    have hcomp : g'.comp (algebraMap R (↥(B.unop).obj)) =
        algebraMap R (↥(A.unop).obj) := by
      have h := congrArg CommRingCat.Hom.hom hcomm
      simp only [CommRingCat.hom_ofHom, CommRingCat.hom_comp] at h
      exact h
    let ψ : ↥(B.unop).obj →ₐ[R] ↥(A.unop).obj :=
      { toRingHom := g'
        commutes' := fun x => by
          have h := congrFun (congrArg DFunLike.coe hcomp) x
          simpa [RingHom.comp_apply] using h }
    let ghom : B.unop ⟶ A.unop := InducedCategory.homMk (CommAlgCat.ofHom ψ)
    refine ⟨ghom.op, ?_⟩
    apply MorphismProperty.CostructuredArrow.Hom.ext
    show (Opposite.op (CommRingCat.ofHom (CommRingCat.Hom.hom φ.left.unop)) : _) = φ.left
    rw [CommRingCat.ofHom_hom]
    exact Quiver.Hom.op_unop φ.left

end Gen
