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

/-- If e : I + J = 1 and I ∩ J = 0 for ideals of a commutative ring B, then
B is isomorphic as a K-algebra to B/I × B/J. -/
noncomputable def algEquiv_prod_quotient_of_isCompl {B : Type u} [CommRing B] [Algebra K B]
    (I J : Ideal B) (h : IsCompl I J) :
    B ≃ₐ[K] (B ⧸ I) × (B ⧸ J) := by
  have hcop : IsCoprime I J := Ideal.isCoprime_iff_sup_eq.mpr h.sup_eq_top
  have hinf : I ⊓ J = ⊥ := h.inf_eq_bot
  let eRing : B ≃+* (B ⧸ I) × (B ⧸ J) :=
    (AlgEquiv.quotientBot K B).symm.toRingEquiv.trans
      ((Ideal.quotientEquivAlgOfEq K hinf.symm).toRingEquiv.trans
        (Ideal.quotientInfEquivQuotientProd I J hcop))
  refine AlgEquiv.ofRingEquiv (f := eRing) ?_
  intro x
  show (Ideal.quotientInfEquivQuotientProd I J hcop) ((AlgEquiv.quotientBot K B).symm.toRingEquiv.trans
      ((Ideal.quotientEquivAlgOfEq K hinf.symm).toRingEquiv))
      (algebraMap K B x) = algebraMap K ((B ⧸ I) × (B ⧸ J)) x
  rw [RingEquiv.trans_apply, RingEquiv.trans_apply]
  rw [(AlgEquiv.quotientBot K B).symm.commutes]
  rw [(Ideal.quotientEquivAlgOfEq K hinf.symm).commutes]
  rw [← Ideal.Quotient.mk_algebraMap (I := I ⊓ J)]
  ext
  · rw [Ideal.quotientInfEquivQuotientProd_fst, ← Ideal.Quotient.mk_algebraMap (I := I)]
    rfl
  · rw [Ideal.quotientInfEquivQuotientProd_snd, ← Ideal.Quotient.mk_algebraMap (I := J)]
    rfl

end S1771
