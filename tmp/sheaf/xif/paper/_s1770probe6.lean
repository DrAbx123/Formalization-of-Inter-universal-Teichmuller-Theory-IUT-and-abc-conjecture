import Mathlib.RingTheory.Etale.Finite
import Mathlib.CategoryTheory.SingleObj
import Mathlib.CategoryTheory.Limits.FullSubcategory

noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace Probe
universe u

variable {K : Type u} [Field K]

-- 1. Is the projection of ConcreteCategory.ofHom rfl?
example {X Y : CommAlgCat.{u} K} (f : X →ₐ[K] Y) :
    (ConcreteCategory.ofHom (C := CommAlgCat.{u} K) f).hom = f := rfl

example {X Y : CommAlgCat.{u} K} (f : X →ₐ[K] Y) :
    (ConcreteCategory.ofHom (C := CommAlgCat.{u} K) f).hom = f :=
  ConcreteCategory.hom_ofHom f

-- 2. Is CommAlgCat.of K X equal to X for arbitrary X?
example (X : CommAlgCat.{u} K) : CommAlgCat.of K X = X := rfl

-- 3. structure literal for morphisms in a full subcategory
example (P : ObjectProperty (CommAlgCat.{u} K)) (X Y : P.FullSubcategory) (f : X.obj ⟶ Y.obj) :
    X ⟶ Y := { hom := f }

-- 4. element API after AlgHom.ext following CommAlgCat.hom_ext
variable (G : Type u) [Group G]
variable (F : (SingleObj G)ᵒᵖ ⥤ CommAlgCat.FiniteEtale.{u} K)

def j0 : (SingleObj G)ᵒᵖ := Opposite.op (SingleObj.star G)

example (S : Subalgebra K (F.obj (j0 G))) (j j' : (SingleObj G)ᵒᵖ) (f : j ⟶ j') :
    True := by
  have key : (ConcreteCategory.ofHom (C := CommAlgCat.{u} K)
      (Subalgebra.val S : ↥S →ₐ[K] (F.obj j').obj)) =
      (ConcreteCategory.ofHom (C := CommAlgCat.{u} K)
        (Subalgebra.val S : ↥S →ₐ[K] (F.obj j).obj) ≫ (F.map f).hom) := by
    apply CommAlgCat.hom_ext
    simp only [ConcreteCategory.hom_ofHom, CommAlgCat.hom_comp]
    apply AlgHom.ext
    intro x
    trivial
  trivial

end Probe
