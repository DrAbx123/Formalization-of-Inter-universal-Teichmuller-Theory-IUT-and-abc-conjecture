import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Etale.Pi
import Mathlib.Algebra.Algebra.Prod

universe u
variable {K : Type u} [Field K]
variable {B : Type u} [CommRing B] [Algebra K B]
variable (I J : Ideal B) (h : IsCompl I J)

example : B ⧸ (I ⊓ J) ≃ₐ[K] (B ⧸ I) × (B ⧸ J) := by
  have hcop : IsCoprime I J := Ideal.isCoprime_iff_sup_eq.mpr h.sup_eq_top
  let e2 : B ⧸ (I ⊓ J) ≃ₐ[K] (B ⧸ I) × (B ⧸ J) :=
    AlgEquiv.ofRingEquiv (f := Ideal.quotientInfEquivQuotientProd I J hcop) (by
      intro x
      sorry)
  exact e2
