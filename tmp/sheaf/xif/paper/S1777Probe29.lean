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

namespace Probe29

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

@[simp] lemma obj_left (A : Algᵒᵖ) :
    (obj A).left = Opposite.op (CommRingCat.of (↥A.unop)) := rfl
@[simp] lemma obj_hom (A : Algᵒᵖ) : (obj A).hom = structMap A.unop := rfl

lemma sliceHom_algMap_comp {A B : Algᵒᵖ} (φ : obj A ⟶ obj B) :
    CommRingCat.ofHom (algebraMap R (↥B.unop)) ≫ φ.left.unop =
      CommRingCat.ofHom (algebraMap R (↥A.unop)) := by
  have htri : Scheme.Spec.map φ.left ≫ (obj B).hom = (obj A).hom := φ.w
  have hgoal : Spec.map (CommRingCat.ofHom (algebraMap R (↥B.unop)) ≫ φ.left.unop) =
      Spec.map (CommRingCat.ofHom (algebraMap R (↥A.unop))) := by
    rw [Spec.map_comp]
    exact htri
  exact Spec.map_injective hgoal

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

instance sliceFunctor_full : sliceFunctor.Full where
  map_surjective {A B} φ := by
    have hcomm : CommRingCat.ofHom (algebraMap R (↥B.unop)) ≫ φ.left.unop =
        CommRingCat.ofHom (algebraMap R (↥A.unop)) := sliceHom_algMap_comp φ
    let g' : ↥(B.unop).obj →+* ↥(A.unop).obj := CommRingCat.Hom.hom φ.left.unop
    have hcomp : g'.comp (algebraMap R (↥(B.unop).obj)) = algebraMap R (↥(A.unop).obj) := by
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

end Probe29
