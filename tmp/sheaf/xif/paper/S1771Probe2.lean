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

/-- A finite etale K-algebra is reduced. -/
instance finiteEtale_isReduced (A : Type u) [CommRing A] [Algebra K A] [Module.Finite K A]
    [Algebra.Etale K A] : IsReduced A :=
  Algebra.FormallyUnramified.isReduced_of_field K A

/-- A finite etale K-algebra is Artinian. -/
instance finiteEtale_isArtinian (A : Type u) [CommRing A] [Algebra K A] [Module.Finite K A]
    [Algebra.Etale K A] : IsArtinianRing A := by
  have := Algebra.FormallyUnramified.finite_of_free K A
  exact isArtinian_of_tower K inferInstance

/-- A finite etale K-algebra is a semisimple ring. -/
instance finiteEtale_isSemisimple (A : Type u) [CommRing A] [Algebra K A] [Module.Finite K A]
    [Algebra.Etale K A] : IsSemisimpleRing A :=
  IsArtinianRing.isSemisimpleRing_of_isReduced A

/-- If e : I + J = 1 and I ∩ J = 0 for ideals of a commutative ring B, then
B is isomorphic as a K-algebra to B/I × B/J. -/
theorem algEquiv_prod_quotient_of_isCompl {B : Type u} [CommRing B] [Algebra K B]
    (I J : Ideal B) (h : IsCompl I J) :
    B ≃ₐ[K] (B ⧸ I) × (B ⧸ J) := by
  have hcop : IsCoprime I J := Ideal.isCoprime_iff_sup_eq.mpr h.sup_eq_top
  have hinf : I ⊓ J = ⊥ := h.inf_eq_bot
  -- the ring equivalence B ≃ (B/I) × (B/J)
  let eRing : B ≃+* (B ⧸ I) × (B ⧸ J) :=
    (AlgEquiv.quotientBot K B).symm.toRingEquiv.trans
      ((Ideal.quotientEquivAlgOfEq K hinf.symm).toRingEquiv.trans
        (Ideal.quotientInfEquivQuotientProd I J hcop))
  refine AlgEquiv.ofRingEquiv (f := eRing) ?_
  intro x
  -- Reduce to the statement for the composite, which is natural.
  have h1 : (AlgEquiv.quotientBot K B).symm (algebraMap K B x) =
      algebraMap K (B ⧸ (⊥ : Ideal B)) x := (AlgEquiv.quotientBot K B).symm.commutes x
  have h2 : (Ideal.quotientEquivAlgOfEq K hinf.symm) (algebraMap K (B ⧸ (⊥ : Ideal B)) x) =
      algebraMap K (B ⧸ (I ⊓ J)) x := (Ideal.quotientEquivAlgOfEq K hinf.symm).commutes x
  have h3 : (Ideal.quotientInfEquivQuotientProd I J hcop) (algebraMap K (B ⧸ (I ⊓ J)) x) =
      algebraMap K ((B ⧸ I) × (B ⧸ J)) x := by
    rw [← Ideal.Quotient.mk_algebraMap]
    ext
    · rw [Ideal.quotientInfEquivQuotientProd_fst]
      rfl
    · rw [Ideal.quotientInfEquivQuotientProd_snd]
      rfl
  exact h1.trans (h2.trans h3)

end S1771
