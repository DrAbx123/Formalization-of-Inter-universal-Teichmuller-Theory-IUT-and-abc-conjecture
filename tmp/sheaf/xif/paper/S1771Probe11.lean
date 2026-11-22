import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.Ideal.Quotient.Operations

universe u
variable {K : Type u} [Field K]
variable {B : Type u} [CommRing B] [Algebra K B]
variable (I J : Ideal B)

#check (I ⊓ J : Ideal B)
#check (B ⧸ (I ⊓ J))
#check (B ⧸ I)
#check ((B ⧸ I) × (B ⧸ J))
#check (B ⧸ (I ⊓ J) ≃ₐ[K] (B ⧸ I) × (B ⧸ J))
