/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# S1745: finite etale K-algebras are closed under finite products and pushouts

This file proves the two closure instances needed to transport the limits/colimits of
CommAlgCat K to the full subcategory CommAlgCat.FiniteEtale K of finite etale algebras:

* (CommAlgCat.finiteEtale K).IsClosedUnderLimitsOfShape (Discrete J) for finite J
  (the product of finite etale algebras is the Pi algebra, Mathlib's AlgHom.pi);
* (CommAlgCat.finiteEtale K).IsClosedUnderColimitsOfShape WalkingSpan
  (the pushout of B <-- A --> C is the tensor product B (x)_A C).

As a consequence (CommAlgCat.FiniteEtale K)^op has finite coproducts and pullbacks.
-/
import Mathlib.RingTheory.Etale.Finite
import Mathlib.CategoryTheory.ObjectProperty.LimitsOfShape
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.Algebra.Category.CommAlgCat.Monoidal
import Mathlib.RingTheory.IsTensorProduct

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace S1745

variable {K : Type} [Field K]

/-- The opposite of the category of finite etale K-algebras (Galois category of S1739). -/
abbrev FiniteEtaleAlg (K : Type) [Field K] : Type 1 := (CommAlgCat.FiniteEtale.{0} K)ᵒᵖ

namespace FiniteEtaleClosure

/-! ### 1. Closedness under isomorphisms -/

instance : (CommAlgCat.finiteEtale K : ObjectProperty (CommAlgCat.{0} K)).IsClosedUnderIsomorphisms where
  of_iso := by
    rintro X Y e ⟨hf, he⟩
    exact ⟨Module.Finite.equiv (CommAlgCat.algEquivOfIso e).toLinearEquiv,
      Algebra.Etale.of_equiv (CommAlgCat.algEquivOfIso e)⟩

/-! ### 2. Finite products: the Pi algebra -/

/-- The Pi-algebra is the categorical product in CommAlgCat K. -/
noncomputable def piFan (J : Type) (A : J → CommAlgCat.{0} K) : Fan A :=
  Fan.mk (CommAlgCat.of K (∀ j, (A j : Type))) fun j =>
    CommAlgCat.ofHom (Pi.evalAlgHom K (fun j => (A j : Type)) j)

lemma piFan_proj_apply (J : Type) (A : J → CommAlgCat.{0} K) (j : J)
    (x : (piFan J A).pt) : ((piFan J A).proj j).hom x = x j := rfl

noncomputable def piFan_isLimit (J : Type) (A : J → CommAlgCat.{0} K) : IsLimit (piFan J A) := by
  refine Fan.IsLimit.mk _ (fun s => CommAlgCat.ofHom (AlgHom.pi fun j => (s.proj j).hom)) ?_ ?_
  · intro s j
    ext x
    rfl
  · intro s m hm
    ext x
    funext j
    have h := congrArg (fun f => (f : s.pt ⟶ A j).hom x) (hm j)
    simp only [CommAlgCat.hom_comp, AlgHom.comp_apply] at h
    rw [piFan_proj_apply] at h
    exact h

theorem finiteEtale_piFan_pt (J : Type) [Fintype J] (A : J → CommAlgCat.{0} K)
    (hA : ∀ j, (CommAlgCat.finiteEtale K) (A j)) :
    (CommAlgCat.finiteEtale K) (piFan J A).pt := by
  haveI : ∀ j, Module.Finite K (A j : Type) := fun j => (hA j).1
  haveI : ∀ j, Algebra.Etale K (A j : Type) := fun j => (hA j).2
  refine ⟨?_, ?_⟩
  · show Module.Finite K (∀ j, (A j : Type))
    infer_instance
  · show Algebra.Etale K (∀ j, (A j : Type))
    infer_instance

/-- finiteEtale K is closed under limits of shape Discrete J for finite J. -/
instance isClosedUnderLimitsOfShape_discrete (J : Type) [Fintype J] :
    (CommAlgCat.finiteEtale K : ObjectProperty (CommAlgCat.{0} K)).IsClosedUnderLimitsOfShape
      (Discrete J) := by
  refine ObjectProperty.IsClosedUnderLimitsOfShape.mk' ?_
  rintro X ⟨F, hF⟩
  haveI : HasLimit (Discrete.functor (fun j : J => F.obj (Discrete.mk j))) :=
    hasLimit_of_iso Discrete.natIsoFunctor
  have hpt : (CommAlgCat.finiteEtale K) (piFan J (fun j => F.obj (Discrete.mk j))).pt :=
    finiteEtale_piFan_pt J _ (fun j => hF (Discrete.mk j))
  have hc : IsLimit (piFan J (fun j => F.obj (Discrete.mk j))) := piFan_isLimit J _
  have e1 : limit F ≅ limit (Discrete.functor (fun j : J => F.obj (Discrete.mk j))) :=
    HasLimit.isoOfNatIso Discrete.natIsoFunctor
  have e2 : limit (Discrete.functor (fun j : J => F.obj (Discrete.mk j))) ≅
      (piFan J (fun j => F.obj (Discrete.mk j))).pt :=
    IsLimit.conePointUniqueUpToIso (limit.isLimit _) hc
  exact ObjectProperty.prop_of_iso _ (e1 ≪≫ e2).symm hpt

/-! ### 3. Pushouts: the tensor product B (x)_A C -/

section Pushout

variable {A B C : CommAlgCat.{0} K} (f : A ⟶ B) (g : A ⟶ C)

/-- The tensor product cocone of a span in CommAlgCat K. -/
noncomputable def tensorCocone : PushoutCocone f g :=
  letI : Algebra (A : Type) (B : Type) := f.hom.toRingHom.toAlgebra
  letI : Algebra (A : Type) (C : Type) := g.hom.toRingHom.toAlgebra
  haveI : IsScalarTower K (A : Type) (B : Type) :=
    IsScalarTower.of_algebraMap_eq' (by ext x; exact (f.hom.commutes x).symm)
  haveI : IsScalarTower K (A : Type) (C : Type) :=
    IsScalarTower.of_algebraMap_eq' (by ext x; exact (g.hom.commutes x).symm)
  PushoutCocone.mk
    (CommAlgCat.ofHom (Algebra.TensorProduct.includeLeft (R := (A : Type)) (A := (B : Type))
      (B := (C : Type)) (S := K)))
    (CommAlgCat.ofHom ((Algebra.TensorProduct.includeRight (R := (A : Type)) (A := (B : Type))
      (B := (C : Type))).restrictScalars K))
    (by
      ext x
      have h1 : f.hom x = algebraMap (A : Type) (B : Type) x := rfl
      have h2 : g.hom x = algebraMap (A : Type) (C : Type) x := rfl
      simp only [CommAlgCat.hom_comp, AlgHom.comp_apply]
      rw [h1, h2]
      simp only [CommAlgCat.hom_ofHom, AlgHom.restrictScalars_apply,
        Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply]
      rw [← Algebra.TensorProduct.algebraMap_apply (S := (A : Type)) (R := (A : Type))
        (A := (B : Type)) (B := (C : Type)) (r := x)]
      rw [← Algebra.TensorProduct.algebraMap_apply' (R := (A : Type)) (A := (B : Type))
        (B := (C : Type)) (r := x)])

noncomputable def tensorCocone_isColimit : IsColimit (tensorCocone f g) := by
  letI : Algebra (A : Type) (B : Type) := f.hom.toRingHom.toAlgebra
  letI : Algebra (A : Type) (C : Type) := g.hom.toRingHom.toAlgebra
  haveI : IsScalarTower K (A : Type) (B : Type) :=
    IsScalarTower.of_algebraMap_eq' (by ext x; exact (f.hom.commutes x).symm)
  haveI : IsScalarTower K (A : Type) (C : Type) :=
    IsScalarTower.of_algebraMap_eq' (by ext x; exact (g.hom.commutes x).symm)
  letI : Algebra (C : Type) ((B : Type) ⊗[A] (C : Type)) := Algebra.TensorProduct.rightAlgebra
  haveI : IsScalarTower (A : Type) (C : Type) ((B : Type) ⊗[A] (C : Type)) :=
    Algebra.TensorProduct.right_isScalarTower
  have key : ∀ (s : PushoutCocone f g), ∃ (d : (tensorCocone f g).pt ⟶ s.pt),
      ((tensorCocone f g).inl ≫ d = s.inl) ∧ ((tensorCocone f g).inr ≫ d = s.inr) ∧
      (∀ (m : (tensorCocone f g).pt ⟶ s.pt), (tensorCocone f g).inl ≫ m = s.inl →
        (tensorCocone f g).inr ≫ m = s.inr → m = d) := by
    intro s
    letI : Algebra (A : Type) (s.pt : Type) :=
      (s.inl.hom.toRingHom.comp (algebraMap (A : Type) (B : Type))).toAlgebra
    have hcomp : (algebraMap (A : Type) (s.pt : Type)) =
        s.inl.hom.toRingHom.comp (algebraMap (A : Type) (B : Type)) := rfl
    haveI : IsScalarTower K (A : Type) (s.pt : Type) :=
      IsScalarTower.of_algebraMap_eq' (by
        ext x
        rw [hcomp]
        simp only [RingHom.comp_apply]
        rw [← IsScalarTower.algebraMap_apply K (A : Type) (B : Type) x]
        exact (s.inl.hom.commutes x).symm)
    haveI hpush : Algebra.IsPushout (A : Type) (B : Type) (C : Type)
        ((B : Type) ⊗[A] (C : Type)) := inferInstance
    let f' : (B : Type) →ₐ[A] (s.pt : Type) := { s.inl.hom with commutes' := fun a => rfl }
    let g' : (C : Type) →ₐ[A] (s.pt : Type) :=
      { s.inr.hom with
        commutes' := fun a => by
          have h := congrArg (fun (φ : A ⟶ s.pt) => φ.hom a) s.condition
          exact h.symm }
    refine ⟨CommAlgCat.ofHom ((Algebra.pushoutDesc ((B : Type) ⊗[A] (C : Type)) f' g'
      (fun x y => mul_comm (f' x) (g' y))).restrictScalars K), ?_, ?_, ?_⟩
    · ext b
      have h := AlgHom.congr_fun (Algebra.lift_algHom_comp_left (S' := (B : Type) ⊗[A] (C : Type))
        f' g' (fun x y => mul_comm (f' x) (g' y))) b
      show ((Algebra.pushoutDesc ((B : Type) ⊗[A] (C : Type)) f' g'
        (fun x y => mul_comm (f' x) (g' y))).comp
          (IsScalarTower.toAlgHom (A : Type) (B : Type) ((B : Type) ⊗[A] (C : Type)))) b =
          s.inl.hom b
      rw [h]
      rfl
    · ext c
      have h := AlgHom.congr_fun (Algebra.lift_algHom_comp_right (S' := (B : Type) ⊗[A] (C : Type))
        f' g' (fun x y => mul_comm (f' x) (g' y))) c
      show ((Algebra.pushoutDesc ((B : Type) ⊗[A] (C : Type)) f' g'
        (fun x y => mul_comm (f' x) (g' y))).comp
          (IsScalarTower.toAlgHom (A : Type) (C : Type) ((B : Type) ⊗[A] (C : Type)))) c =
          s.inr.hom c
      rw [h]
      rfl
    · intro m hm1 hm2
      let m' : ((B : Type) ⊗[A] (C : Type)) →ₐ[A] (s.pt : Type) :=
        { m.hom with
          commutes' := fun a => by
            show m.hom (algebraMap (A : Type) ((B : Type) ⊗[A] (C : Type)) a) =
              algebraMap (A : Type) (s.pt : Type) a
            have h := congrArg (fun (φ : B ⟶ s.pt) =>
              φ.hom (algebraMap (A : Type) (B : Type) a)) hm1
            exact h }
      have h1 : m'.comp (IsScalarTower.toAlgHom (A : Type) (C : Type) ((B : Type) ⊗[A] (C : Type)))
          = g' := by
        ext c
        show m.hom (algebraMap (C : Type) ((B : Type) ⊗[A] (C : Type)) c) = s.inr.hom c
        have h := congrArg (fun (φ : C ⟶ s.pt) => φ.hom c) hm2
        exact h
      have h2 : m'.comp (IsScalarTower.toAlgHom (A : Type) (B : Type) ((B : Type) ⊗[A] (C : Type)))
          = f' := by
        ext b
        show m.hom (algebraMap (B : Type) ((B : Type) ⊗[A] (C : Type)) b) = s.inl.hom b
        have h := congrArg (fun (φ : B ⟶ s.pt) => φ.hom b) hm1
        exact h
      have heq : m' = Algebra.pushoutDesc ((B : Type) ⊗[A] (C : Type)) f' g'
          (fun x y => mul_comm (f' x) (g' y)) :=
        Algebra.IsPushout.algHom_ext ((B : Type) ⊗[A] (C : Type))
          (h1.trans (Algebra.lift_algHom_comp_right (S' := (B : Type) ⊗[A] (C : Type))
            f' g' (fun x y => mul_comm (f' x) (g' y))).symm)
          (h2.trans (Algebra.lift_algHom_comp_left (S' := (B : Type) ⊗[A] (C : Type))
            f' g' (fun x y => mul_comm (f' x) (g' y))).symm)
      have hm : m = CommAlgCat.ofHom (m'.restrictScalars K) := rfl
      rw [hm]
      exact congrArg (fun (ψ : ((B : Type) ⊗[A] (C : Type)) →ₐ[A] (s.pt : Type)) =>
        CommAlgCat.ofHom (ψ.restrictScalars K)) heq
  choose d hd1 hd2 hd3 using key
  refine PushoutCocone.IsColimit.mk (tensorCocone f g).condition d hd1 hd2 ?_
  intro s m hm1 hm2
  exact hd3 s m hm1 hm2

/-- The tensor product of finite etale algebras is finite etale. -/
theorem finiteEtale_tensorCocone_pt (hA : (CommAlgCat.finiteEtale K) A)
    (hB : (CommAlgCat.finiteEtale K) B) (hC : (CommAlgCat.finiteEtale K) C) :
    (CommAlgCat.finiteEtale K) (tensorCocone f g).pt := by
  letI : Algebra (A : Type) (B : Type) := f.hom.toRingHom.toAlgebra
  letI : Algebra (A : Type) (C : Type) := g.hom.toRingHom.toAlgebra
  haveI : IsScalarTower K (A : Type) (B : Type) :=
    IsScalarTower.of_algebraMap_eq' (by ext x; exact (f.hom.commutes x).symm)
  haveI : IsScalarTower K (A : Type) (C : Type) :=
    IsScalarTower.of_algebraMap_eq' (by ext x; exact (g.hom.commutes x).symm)
  haveI : Module.Finite K (A : Type) := hA.1
  haveI : Module.Finite K (B : Type) := hB.1
  haveI : Module.Finite K (C : Type) := hC.1
  haveI : Algebra.Etale K (A : Type) := hA.2
  haveI : Algebra.Etale K (B : Type) := hB.2
  haveI : Algebra.Etale K (C : Type) := hC.2
  refine ⟨?_, ?_⟩
  · show Module.Finite K ((B : Type) ⊗[A] (C : Type))
    haveI : Module.Finite (A : Type) (B : Type) :=
      Module.Finite.of_restrictScalars_finite K (A : Type) (B : Type)
    haveI : Module.Finite (A : Type) (C : Type) :=
      Module.Finite.of_restrictScalars_finite K (A : Type) (C : Type)
    haveI : Module.Finite (A : Type) ((B : Type) ⊗[A] (C : Type)) :=
      Module.Finite.tensorProduct (A : Type) (B : Type) (C : Type)
    exact Module.Finite.trans (A : Type) ((B : Type) ⊗[A] (C : Type))
  · show Algebra.Etale K ((B : Type) ⊗[A] (C : Type))
    haveI : Algebra.Etale (A : Type) (C : Type) :=
      Algebra.Etale.of_restrictScalars K (A : Type) (C : Type)
    haveI : Algebra.Etale (B : Type) ((B : Type) ⊗[A] (C : Type)) :=
      Algebra.Etale.baseChange (A : Type) (C : Type) (B : Type)
    exact Algebra.Etale.comp K (B : Type) ((B : Type) ⊗[A] (C : Type))

end Pushout

/-- finiteEtale K is closed under pushouts: the pushout is the tensor product over the
common vertex. -/
instance isClosedUnderColimitsOfShape_walkingSpan :
    (CommAlgCat.finiteEtale K : ObjectProperty (CommAlgCat.{0} K)).IsClosedUnderColimitsOfShape
      WalkingSpan := by
  refine ObjectProperty.IsClosedUnderColimitsOfShape.mk' ?_
  rintro X ⟨F, hF⟩
  let f := F.map WalkingSpan.Hom.fst
  let g := F.map WalkingSpan.Hom.snd
  letI : Algebra (F.obj WalkingSpan.zero : Type) (F.obj WalkingSpan.left : Type) :=
    f.hom.toRingHom.toAlgebra
  letI : Algebra (F.obj WalkingSpan.zero : Type) (F.obj WalkingSpan.right : Type) :=
    g.hom.toRingHom.toAlgebra
  haveI : IsScalarTower K (F.obj WalkingSpan.zero : Type) (F.obj WalkingSpan.left : Type) :=
    IsScalarTower.of_algebraMap_eq' (by ext x; exact (f.hom.commutes x).symm)
  haveI : IsScalarTower K (F.obj WalkingSpan.zero : Type) (F.obj WalkingSpan.right : Type) :=
    IsScalarTower.of_algebraMap_eq' (by ext x; exact (g.hom.commutes x).symm)
  have hpt : (CommAlgCat.finiteEtale K) (tensorCocone f g).pt :=
    finiteEtale_tensorCocone_pt f g (hF WalkingSpan.zero) (hF WalkingSpan.left) (hF WalkingSpan.right)
  have hc : IsColimit ((Cocone.precompose (diagramIsoSpan F).hom).obj (tensorCocone f g)) :=
    (IsColimit.precomposeHomEquiv (diagramIsoSpan F) (tensorCocone f g)).symm
      (tensorCocone_isColimit f g)
  have e : colimit F ≅ (tensorCocone f g).pt := colimit.isoColimitCocone ⟨_, hc⟩
  exact ObjectProperty.prop_of_iso _ e.symm hpt

/-! ### 4. Assembly: finite coproducts and pullbacks -/

instance hasFiniteProducts : HasFiniteProducts (CommAlgCat.FiniteEtale.{0} K) where
  out n := by
    haveI : HasLimitsOfShape (Discrete (Fin n)) (CommAlgCat.FiniteEtale.{0} K) :=
      hasLimitsOfShape_of_closedUnderLimits (Discrete (Fin n)) (CommAlgCat.finiteEtale K)
    infer_instance

instance hasColimitsOfShape_walkingSpan_finiteEtale :
    HasColimitsOfShape WalkingSpan (CommAlgCat.FiniteEtale.{0} K) :=
  hasColimitsOfShape_of_closedUnderColimits WalkingSpan (CommAlgCat.finiteEtale K)

/-- The opposite of the category of finite etale K-algebras has finite coproducts. -/
instance hasFiniteCoproducts : HasFiniteCoproducts (FiniteEtaleAlg K) where
  out n := by
    haveI h1 : HasLimitsOfShape (Discrete (Fin n)) (CommAlgCat.FiniteEtale.{0} K) :=
      HasFiniteProducts.out n
    haveI h2 : HasLimitsOfShape ((Discrete (Fin n))ᵒᵖ) (CommAlgCat.FiniteEtale.{0} K) :=
      hasLimitsOfShape_of_equivalence (Discrete.opposite (Fin n)).symm
    exact hasColimitsOfShape_op_of_hasLimitsOfShape (J := Discrete (Fin n))

/-- The opposite of the category of finite etale K-algebras has pullbacks. -/
instance hasPullbacks : HasPullbacks (FiniteEtaleAlg K) := by
  haveI : HasColimitsOfShape WalkingCospanᵒᵖ (CommAlgCat.FiniteEtale.{0} K) :=
    hasColimitsOfShape_of_equivalence walkingCospanOpEquiv.symm
  exact hasLimitsOfShape_op_of_hasColimitsOfShape (J := WalkingCospan)


/-! ### 5. Axiom audit and remarks -/

/-!
#### Remark on the shape of the colimit closure

For the Galois category FiniteEtaleAlg K = (CommAlgCat.FiniteEtale K)^op we need
HasPullbacks (FiniteEtaleAlg K).  Since HasPullbacks C is *defined* as
HasLimitsOfShape WalkingCospan C, pullbacks in C^op correspond to colimits of shape
WalkingCospan^op in C, and WalkingCospan^op is equivalent to WalkingSpan
(walkingCospanOpEquiv).  Hence the relevant closure instance is
IsClosedUnderColimitsOfShape WalkingSpan (pushouts), which is what is proved in
Section 3.  The instance for WalkingCospan is not needed here: a WalkingCospan-shaped
diagram is a cospan B --> A <-- C, and *its colimit is the apex* (the shape has a
terminal object), so that instance is a trivial consequence of closedness under
isomorphisms.  What is *not* trivial is closedness under WalkingSpan-shaped colimits,
which is the pushouts = tensor products statement proved above.
-/

#print axioms S1745.FiniteEtaleClosure.piFan_isLimit
#print axioms S1745.FiniteEtaleClosure.finiteEtale_piFan_pt
#print axioms S1745.FiniteEtaleClosure.isClosedUnderLimitsOfShape_discrete
#print axioms S1745.FiniteEtaleClosure.tensorCocone_isColimit
#print axioms S1745.FiniteEtaleClosure.finiteEtale_tensorCocone_pt
#print axioms S1745.FiniteEtaleClosure.isClosedUnderColimitsOfShape_walkingSpan
#print axioms S1745.FiniteEtaleClosure.hasFiniteProducts
#print axioms S1745.FiniteEtaleClosure.hasFiniteCoproducts
#print axioms S1745.FiniteEtaleClosure.hasPullbacks

end FiniteEtaleClosure

end S1745