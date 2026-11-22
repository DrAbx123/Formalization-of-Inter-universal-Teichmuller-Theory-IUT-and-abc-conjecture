import Mathlib.RingTheory.Etale.Finite
import Mathlib.CategoryTheory.ObjectProperty.LimitsOfShape
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.Algebra.Category.CommAlgCat.Monoidal
import Mathlib.RingTheory.IsTensorProduct

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace S1745

variable (K : Type) [Field K]

namespace FiniteEtaleClosure

instance : (CommAlgCat.finiteEtale K : ObjectProperty (CommAlgCat.{0} K)).IsClosedUnderIsomorphisms where
  of_iso := by
    rintro X Y e ⟨hf, he⟩
    exact ⟨Module.Finite.equiv (CommAlgCat.algEquivOfIso e).toLinearEquiv,
      Algebra.Etale.of_equiv (CommAlgCat.algEquivOfIso e)⟩

/-- The Pi-algebra is the categorical product in CommAlgCat K. -/
noncomputable def piFan (J : Type) (A : J → CommAlgCat.{0} K) : Fan A :=
  Fan.mk (CommAlgCat.of K (∀ j, (A j : Type))) fun j =>
    CommAlgCat.ofHom (Pi.evalAlgHom K (fun j => (A j : Type)) j)

def piFan_isLimit (J : Type) (A : J → CommAlgCat.{0} K) : IsLimit (piFan K J A) := by
  refine Fan.IsLimit.mk _ (fun s => CommAlgCat.ofHom (AlgHom.pi fun j => (s.proj j).hom)) ?_ ?_
  · intro s j
    ext x
    rfl
  · intro s m hm
    ext x
    simp only [CommAlgCat.hom_ofHom, AlgHom.pi_apply]
    funext j
    have h := congrArg (fun f => (f : s.pt ⟶ A j).hom x) (hm j)
    simpa [piFan] using h

theorem finiteEtale_piFan_pt (J : Type) [Fintype J] (A : J → CommAlgCat.{0} K)
    (hA : ∀ j, (CommAlgCat.finiteEtale K) (A j)) :
    (CommAlgCat.finiteEtale K) (piFan K J A).pt := by
  haveI : ∀ j, Module.Finite K (A j : Type) := fun j => (hA j).1
  haveI : ∀ j, Algebra.Etale K (A j : Type) := fun j => (hA j).2
  refine ⟨?_, ?_⟩
  · change Module.Finite K (↑(piFan K J A).pt)
    infer_instance
  · change Algebra.Etale K (↑(piFan K J A).pt)
    infer_instance

instance isClosedUnderLimitsOfShape_discrete (J : Type) [Fintype J] :
    (CommAlgCat.finiteEtale K : ObjectProperty (CommAlgCat.{0} K)).IsClosedUnderLimitsOfShape
      (Discrete J) := by
  refine ObjectProperty.IsClosedUnderLimitsOfShape.mk' ?_
  rintro X ⟨F, hF⟩
  haveI : HasLimit (Discrete.functor (fun j : J => F.obj (Discrete.mk j))) :=
    hasLimit_of_iso Discrete.natIsoFunctor
  have hpt : (CommAlgCat.finiteEtale K) (piFan K J (fun j => F.obj (Discrete.mk j))).pt :=
    finiteEtale_piFan_pt K J _ (fun j => hF (Discrete.mk j))
  have hc : IsLimit (piFan K J (fun j => F.obj (Discrete.mk j))) := piFan_isLimit K J _
  have e1 : limit F ≅ limit (Discrete.functor (fun j : J => F.obj (Discrete.mk j))) :=
    HasLimit.isoOfNatIso Discrete.natIsoFunctor
  have e2 : limit (Discrete.functor (fun j : J => F.obj (Discrete.mk j))) ≅
      (piFan K J (fun j => F.obj (Discrete.mk j))).pt :=
    IsLimit.conePointUniqueUpToIso (limit.isLimit _) hc
  exact ObjectProperty.prop_of_iso _ (e1 ≪≫ e2).symm hpt

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
      show (algebraMap (A : Type) (B : Type) x) ⊗ₜ (1 : (C : Type)) =
        (1 : (B : Type)) ⊗ₜ (algebraMap (A : Type) (C : Type) x)
      rw [← Algebra.TensorProduct.algebraMap_apply (S := (A : Type)) (R := (A : Type))
        (A := (B : Type)) (B := (C : Type)) (r := x)]
      rw [← Algebra.TensorProduct.algebraMap_apply' (R := (A : Type)) (A := (B : Type))
        (B := (C : Type)) (r := x)])

theorem tensorCocone_isColimit : IsColimit (tensorCocone f g) := by
  letI : Algebra (A : Type) (B : Type) := f.hom.toRingHom.toAlgebra
  letI : Algebra (A : Type) (C : Type) := g.hom.toRingHom.toAlgebra
  haveI : IsScalarTower K (A : Type) (B : Type) :=
    IsScalarTower.of_algebraMap_eq' (by ext x; exact (f.hom.commutes x).symm)
  haveI : IsScalarTower K (A : Type) (C : Type) :=
    IsScalarTower.of_algebraMap_eq' (by ext x; exact (g.hom.commutes x).symm)
  have key : ∀ (s : PushoutCocone f g), ∃ (d : (tensorCocone f g).pt ⟶ s.pt),
      ((tensorCocone f g).inl ≫ d = s.inl) ∧ ((tensorCocone f g).inr ≫ d = s.inr) ∧
      (∀ (m : (tensorCocone f g).pt ⟶ s.pt), (tensorCocone f g).inl ≫ m = s.inl →
        (tensorCocone f g).inr ≫ m = s.inr → m = d) := by
    intro s
    letI : Algebra (A : Type) (s.pt : Type) :=
      (s.inl.hom.comp (algebraMap (A : Type) (B : Type))).toRingHom.toAlgebra
    haveI : IsScalarTower K (A : Type) (s.pt : Type) :=
      IsScalarTower.of_algebraMap_eq' (by
        ext x
        show s.inl.hom (algebraMap (A : Type) (B : Type) (algebraMap K (A : Type) x)) =
          algebraMap K (s.pt : Type) x
        rw [IsScalarTower.algebraMap_apply K (A : Type) (B : Type) x, s.inl.hom.commutes])
    haveI hpush : Algebra.IsPushout (A : Type) (B : Type) (C : Type)
        ((B : Type) ⊗[A] (C : Type)) := inferInstance
    let f' : (B : Type) →ₐ[A : Type] (s.pt : Type) := { s.inl.hom with commutes' := fun a => rfl }
    let g' : (C : Type) →ₐ[A : Type] (s.pt : Type) :=
      { s.inr.hom with
        commutes' := fun a => by
          have h := congrArg (fun (φ : A ⟶ s.pt) => (φ.hom : (A : Type) → (s.pt : Type)) a)
            s.condition
          exact h.symm }
    refine ⟨CommAlgCat.ofHom ((Algebra.pushoutDesc ((B : Type) ⊗[A] (C : Type)) f' g'
      (fun x y => Commute.all _ _)).restrictScalars K), ?_, ?_, ?_⟩
    · ext b
      have h := AlgHom.congr_fun (Algebra.lift_algHom_comp_left (S' := (B : Type) ⊗[A] (C : Type))
        f' g' (fun x y => Commute.all _ _)) b
      simpa using h
    · ext c
      have h := AlgHom.congr_fun (Algebra.lift_algHom_comp_right (S' := (B : Type) ⊗[A] (C : Type))
        f' g' (fun x y => Commute.all _ _)) c
      simpa using h
    · intro m hm1 hm2
      let m' : ((B : Type) ⊗[A] (C : Type)) →ₐ[A : Type] (s.pt : Type) :=
        { m.hom with
          commutes' := fun a => by
            have h := congrArg (fun (φ : A ⟶ s.pt) => (φ.hom : (A : Type) → (s.pt : Type)) a) hm1
            exact h }
      have h1 : m'.comp (IsScalarTower.toAlgHom (A : Type) (C : Type) ((B : Type) ⊗[A] (C : Type)))
          = g' := by
        ext c
        have h := congrArg (fun (φ : C ⟶ s.pt) => (φ.hom : (C : Type) → (s.pt : Type)) c) hm2
        simpa using h.symm
      have h2 : m'.comp (IsScalarTower.toAlgHom (A : Type) (B : Type) ((B : Type) ⊗[A] (C : Type)))
          = f' := by
        ext b
        have h := congrArg (fun (φ : B ⟶ s.pt) => (φ.hom : (B : Type) → (s.pt : Type)) b) hm1
        simpa using h.symm
      exact h1 ▸ h2 ▸ rfl
  choose d hd1 hd2 hd3 using key
  refine PushoutCocone.IsColimit.mk (tensorCocone f g).w d hd1 hd2 ?_
  intro s m hm1 hm2
  exact hd3 s m hm1 hm2

end Pushout

end FiniteEtaleClosure

end S1745
