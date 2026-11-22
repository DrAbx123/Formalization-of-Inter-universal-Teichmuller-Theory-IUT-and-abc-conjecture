import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.SimpleModule.Basic
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
    B ≃ₐ[K] ((B ⧸ I) × (B ⧸ J)) := by
  have hcop : IsCoprime I J := Ideal.isCoprime_iff_sup_eq.mpr h.sup_eq_top
  let φ : B →ₐ[K] ((B ⧸ I) × (B ⧸ J)) :=
    AlgHom.prod (Ideal.Quotient.mkₐ K I) (Ideal.Quotient.mkₐ K J)
  have hcomp : (fun b : B => φ b) =
      fun b => (Ideal.quotientInfEquivQuotientProd I J hcop)
        (Ideal.Quotient.mk (I ⊓ J) b) := by
    funext b
    ext
    · simp [φ, Ideal.quotientInfEquivQuotientProd_fst]
    · simp [φ, Ideal.quotientInfEquivQuotientProd_snd]
  have hmk : Function.Bijective (fun b : B => Ideal.Quotient.mk (I ⊓ J) b) := by
    rw [h.inf_eq_bot]
    convert (AlgEquiv.quotientBot K B).symm.bijective using 1
    ext b
    simp
  have hbij : Function.Bijective φ := by
    change Function.Bijective (fun b => φ b)
    rw [hcomp]
    exact (Ideal.quotientInfEquivQuotientProd I J hcop).bijective.comp hmk
  exact AlgEquiv.ofBijective φ hbij

@[simp]
lemma algEquiv_prod_quotient_of_isCompl_apply {B : Type u} [CommRing B] [Algebra K B]
    (I J : Ideal B) (h : IsCompl I J) (b : B) :
    algEquiv_prod_quotient_of_isCompl (K := K) I J h b =
      (Ideal.Quotient.mk I b, Ideal.Quotient.mk J b) := rfl

end S1771
