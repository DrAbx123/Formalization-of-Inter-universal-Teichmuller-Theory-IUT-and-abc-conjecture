import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Etale.Pi
import Mathlib.Algebra.Algebra.Prod
import Mathlib.Algebra.Category.CommAlgCat.Basic

open CategoryTheory CategoryTheory.Limits

universe u

namespace S1771

variable {K : Type u} [Field K]

/-- If I + J = 1 and I ∩ J = 0 for ideals of a commutative ring B, then
B is isomorphic as a K-algebra to B/I × B/J. -/
noncomputable def algEquiv_prod_quotient_of_isCompl {B : Type u} [CommRing B] [Algebra K B]
    (I J : Ideal B) (h : IsCompl I J) :
    B ≃ₐ[K] (B ⧸ I) × (B ⧸ J) := by
  have hcop : IsCoprime I J := Ideal.isCoprime_iff_sup_eq.mpr h.sup_eq_top
  have hinf : I ⊓ J = ⊥ := h.inf_eq_bot
  have hCRT : ∀ x : K, (Ideal.quotientInfEquivQuotientProd I J hcop)
      (algebraMap K (B ⧸ (I ⊓ J)) x) = algebraMap K ((B ⧸ I) × (B ⧸ J)) x := by
    intro x
    rw [← Ideal.Quotient.mk_algebraMap (R₁ := K) (I := I ⊓ J) x]
    ext
    · rw [Ideal.quotientInfEquivQuotientProd_fst,
        ← Ideal.Quotient.mk_algebraMap (R₁ := K) (I := I) x]
      rfl
    · rw [Ideal.quotientInfEquivQuotientProd_snd,
        ← Ideal.Quotient.mk_algebraMap (R₁ := K) (I := J) x]
      rfl
  let e2 : B ⧸ (I ⊓ J) ≃ₐ[K] (B ⧸ I) × (B ⧸ J) :=
    AlgEquiv.ofRingEquiv (f := Ideal.quotientInfEquivQuotientProd I J hcop) hCRT
  exact (AlgEquiv.quotientBot K B).symm.trans
    ((Ideal.quotientEquivAlgOfEq K hinf.symm).trans e2)

end S1771
