import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.Ideal.Quotient.Operations

universe u
variable {K : Type u} [Field K]
variable {B : Type u} [CommRing B] [Algebra K B]
variable (I J : Ideal B)

#check ((B ⧸ (I ⊓ J)) ≃ₐ[K] ((B ⧸ I) × (B ⧸ J)))
#check (AlgEquiv (B ⧸ (I ⊓ J)) ((B ⧸ I) × (B ⧸ J)) K)
#check @AlgEquiv (B ⧸ (I ⊓ J)) ((B ⧸ I) × (B ⧸ J)) K
