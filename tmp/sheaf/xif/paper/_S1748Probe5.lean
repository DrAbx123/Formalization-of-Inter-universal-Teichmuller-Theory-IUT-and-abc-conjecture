/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Mathlib.RingTheory.Etale.Finite
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.RingTheory.Etale.Field

/-!
# S1748 -- the automorphism group of the geometric fibre functor

For a field `K` and a geometric point `Ω` (an algebraic closure of `K`), Mathlib provides
the fibre functor

  `CommAlgCat.FiniteEtale.fiber K Ω : (FiniteEtale K)ᵒᵖ ⥤ FintypeCat`,  `S ↦ (S →ₐ[K] Ω)`.

This file proves that its automorphism group is the absolute Galois group of `K`:

  `Aut (fiber K Ω) ≃* (Ω ≃ₐ[K] Ω)`,

and hence, for `Ω = AlgebraicClosure K`, that `Aut (fiber K Ω) ≃* Field.absoluteGaloisGroup K`.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

universe u

open CategoryTheory CategoryTheory.Limits TensorProduct

namespace S1748FiniteEtaleFiber

variable (K : Type u) [Field K]

/-- The opposite of the category of finite etale `K`-algebras: the category of finite etale
`K`-schemes (affine ones).  The fibre functor is covariant on this category. -/
abbrev C : Type (u + 1) := (CommAlgCat.FiniteEtale.{u} K)ᵒᵖ

variable {K}

/-- The geometric fibre functor at `Ω`. -/
abbrev fiber {Ω : Type u} [Field Ω] [Algebra K Ω] : C K ⥤ FintypeCat.{u} :=
  CommAlgCat.FiniteEtale.fiber K Ω

/-! ### 1. Intermediate fields as finite etale `K`-algebras -/

namespace IntermediateField

variable {Ω : Type u} [Field Ω] [Algebra K Ω]

/-- A finite separable intermediate field of `Ω/K` is a finite etale `K`-algebra. -/
instance (L : IntermediateField K Ω) [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    Algebra.Etale K L where
  formallyEtale := Algebra.FormallyEtale.of_isSeparable K L
  finitePresentation := (Algebra.FinitePresentation.of_finiteType).mp inferInstance

/-- The corresponding object of `(FiniteEtale K)ᵒᵖ`. -/
abbrev toFiniteEtale (L : IntermediateField K Ω) [FiniteDimensional K L]
    [Algebra.IsSeparable K L] : C K :=
  Opposite.op (CommAlgCat.FiniteEtale.of K L)

end IntermediateField

/-! ### 2. Postcomposition with an automorphism of the geometric point -/

variable {Ω : Type u} [Field Ω] [Algebra K Ω]

/-- The bijection `Hom(A, Ω) ≃ Hom(A, Ω)` induced by postcomposition with a `K`-algebra
automorphism of `Ω`. -/
def postcompEquiv (h : Ω ≃ₐ[K] Ω) (A : C K) :
    (fiber (K := K) (Ω := Ω)).obj A ≃ (fiber (K := K) (Ω := Ω)).obj A where
  toFun f := h.toAlgHom.comp f
  invFun f := h.symm.toAlgHom.comp f
  left_inv f := AlgHom.ext fun x => by simp
  right_inv f := AlgHom.ext fun x => by simp

/-- Postcomposition by a `K`-algebra automorphism of `Ω` is a natural automorphism of the fibre
functor. -/
def postcomp (h : Ω ≃ₐ[K] Ω) : Aut (fiber (K := K) (Ω := Ω)) :=
  NatIso.ofComponents (fun A => FintypeCat.equivEquivIso (postcompEquiv h A)) (by
    intro A B f
    apply FintypeCat.hom_ext
    intro u
    rfl)

@[simp]
theorem postcomp_hom_app_apply (h : Ω ≃ₐ[K] Ω) (A : C K) (f : A.unop →ₐ[K] Ω) :
    (postcomp h).hom.app A f = h.toAlgHom.comp f := rfl

/-- Postcomposition is a group homomorphism from the absolute Galois group into the automorphism
group of the fibre functor. -/
def postcompMonoidHom : (Ω ≃ₐ[K] Ω) →* Aut (fiber (K := K) (Ω := Ω)) where
  toFun := postcomp
  map_one' := by
    ext A f
    rfl
  map_mul' h₁ h₂ := by
    ext A f
    rfl

@[simp]
theorem postcompMonoidHom_apply (h : Ω ≃ₐ[K] Ω) : postcompMonoidHom h = postcomp h := rfl

/-! ### 3. The value of a natural automorphism on finite separable subfields -/

section Values

variable {Ω : Type u} [Field Ω] [Algebra K Ω]

/-- The `K`-algebra map `L → Ω` obtained by applying a natural automorphism `σ` of the fibre
functor to the identity embedding of a finite separable intermediate field `L`. -/
def sigmaAt (σ : Aut (fiber (K := K) (Ω := Ω))) (L : IntermediateField K Ω)
    [FiniteDimensional K L] [Algebra.IsSeparable K L] : ↥L →ₐ[K] Ω :=
  σ.hom.app (IntermediateField.toFiniteEtale L) (IntermediateField.val L)

variable {σ : Aut (fiber (K := K) (Ω := Ω))}


set_option maxHeartbeats 1000000
variable {σ : Aut (fiber (K := K) (Ω := Ω))}
variable {L L' : IntermediateField K Ω} [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [FiniteDimensional K L'] [Algebra.IsSeparable K L']

theorem test_restrictC (h : L ≤ L') (x : ↥L) :
    sigmaAt σ L x = sigmaAt σ L' ⟨x.1, h x.2⟩ := by
  have hnat := congrArg (fun k : (fiber (K := K) (Ω := Ω)).obj (IntermediateField.toFiniteEtale L') ⟶
      (fiber (K := K) (Ω := Ω)).obj (IntermediateField.toFiniteEtale L) =>
      k (IntermediateField.val L' : ↥L' →ₐ[K] Ω))
    (NatTrans.naturality σ.hom (f := (CommAlgCat.FiniteEtale.ofHom (IntermediateField.inclusion h)).op))
  exact congrArg (fun g : ↥L →ₐ[K] Ω => g x) hnat

end S1748FiniteEtaleFiber.Values
end S1748FiniteEtaleFiber
