import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Algebra.Prod

universe u
variable {K : Type u} [Field K]

example (B : Type u) [CommRing B] [Algebra K B] (φ : B →ₐ[K] B)
    (h : Function.Bijective φ) : B ≃ₐ[K] B :=
  AlgEquiv.ofBijective φ h

example (B : Type u) [CommRing B] [Algebra K B] (I J : Ideal B) :
    B ≃ₐ[K] ((B ⧸ I) × (B ⧸ J)) := by
  let φ : B →ₐ[K] ((B ⧸ I) × (B ⧸ J)) :=
    AlgHom.prod (Ideal.Quotient.mkₐ K I) (Ideal.Quotient.mkₐ K J)
  have h : Function.Bijective φ := by sorry
  exact AlgEquiv.ofBijective φ h
