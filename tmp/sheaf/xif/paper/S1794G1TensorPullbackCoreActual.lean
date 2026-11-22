/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.TensorProduct.Maps

/-! # G1 core: universal property of the tensor product of algebras -/

namespace LeanFormal.IUT.GaloisFiberFunctor

open scoped TensorProduct

universe u

variable (A B C Ω : Type u)
variable [CommRing A] [CommRing B] [Algebra A B]
variable [CommRing C] [Algebra A C]
variable [CommRing Ω] [Algebra A Ω]

/-- G1 algebraic core (pullback field, first half): `A`-algebra maps out of the tensor
product `B ⊗[A] C` are exactly pairs of commuting `A`-algebra maps out of `B` and `C`.
This is the universal property behind `Hom_K(B ⊗_A C, Ω) = Hom_K(B,Ω) ×_{Hom_K(A,Ω)} Hom_K(C,Ω)`.
We record it in the form supplied by Mathlib; the categorical packaging as preservation of a
`WalkingCospan` limit cone is the next G1 step. -/
noncomputable def tensorPullbackHomEquiv :
    { fg : (B →ₐ[A] Ω) × (C →ₐ[A] Ω) // ∀ x y, Commute (fg.1 x) (fg.2 y) } ≃
      ((B ⊗[A] C) →ₐ[A] Ω) :=
  Algebra.TensorProduct.liftEquiv

/-- Reading the equivalence on the left inclusion. -/
@[simp] theorem tensorPullbackHomEquiv_includeLeft
    (fg : { fg : (B →ₐ[A] Ω) × (C →ₐ[A] Ω) // ∀ x y, Commute (fg.1 x) (fg.2 y) }) :
    (tensorPullbackHomEquiv A B C Ω fg).comp Algebra.TensorProduct.includeLeft = fg.1.1 :=
  rfl

/-- Reading the equivalence on the right inclusion. -/
@[simp] theorem tensorPullbackHomEquiv_includeRight
    (fg : { fg : (B →ₐ[A] Ω) × (C →ₐ[A] Ω) // ∀ x y, Commute (fg.1 x) (fg.2 y) }) :
    ((tensorPullbackHomEquiv A B C Ω fg).restrictScalars A).comp
        Algebra.TensorProduct.includeRight = fg.1.2 :=
  rfl

end LeanFormal.IUT.GaloisFiberFunctor
