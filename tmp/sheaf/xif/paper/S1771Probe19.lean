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
  have hcomp : (fun b : B => (AlgHom.prod (Ideal.Quotient.mkₐ K I) (Ideal.Quotient.mkₐ K J)) b) =
      fun b => (Ideal.quotientInfEquivQuotientProd I J hcop)
        (Ideal.Quotient.mk (I ⊓ J) b) := by
    funext b
    ext
    · simp [Ideal.quotientInfEquivQuotientProd_fst]
    · simp [Ideal.quotientInfEquivQuotientProd_snd]
  have hmk : Function.Bijective (fun b : B => Ideal.Quotient.mk (I ⊓ J) b) := by
    rw [h.inf_eq_bot]
    convert (AlgEquiv.quotientBot K B).symm.bijective using 1
    ext b
    simp
  have hbij : Function.Bijective (fun b : B =>
      (AlgHom.prod (Ideal.Quotient.mkₐ K I) (Ideal.Quotient.mkₐ K J)) b) := by
    rw [hcomp]
    exact (Ideal.quotientInfEquivQuotientProd I J hcop).bijective.comp hmk
  exact AlgEquiv.ofBijective (R := K)
    (AlgHom.prod (Ideal.Quotient.mkₐ K I) (Ideal.Quotient.mkₐ K J)) hbij

@[simp]
lemma algEquiv_prod_quotient_of_isCompl_apply {B : Type u} [CommRing B] [Algebra K B]
    (I J : Ideal B) (h : IsCompl I J) (b : B) :
    algEquiv_prod_quotient_of_isCompl I J h b =
      (Ideal.Quotient.mk I b, Ideal.Quotient.mk J b) := rfl

/-- A surjective map of finite etale K-algebras is a product projection. -/
noncomputable def exists_prod_algEquiv_of_surjective
    (A B : Type u) [CommRing A] [Algebra K A] [Module.Finite K A] [Algebra.Etale K A]
    [CommRing B] [Algebra K B] [Module.Finite K B] [Algebra.Etale K B]
    (f : B →ₐ[K] A) (hf : Function.Surjective f) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra K C) (_ : Module.Finite K C)
      (_ : Algebra.Etale K C),
      ∃ e : B ≃ₐ[K] (A × C), f = (AlgHom.fst K A C).comp e.toAlgHom := by
  haveI : IsReduced B := Algebra.FormallyUnramified.isReduced_of_field K B
  haveI : IsArtinianRing B := IsArtinianRing.of_finite K B
  haveI : IsSemisimpleRing B := IsArtinianRing.isSemisimpleRing_of_isReduced B
  let I : Ideal B := RingHom.ker f
  obtain ⟨J, hJ⟩ := ComplementedLattice.exists_isCompl I
  obtain ⟨eJ, heJ, hJe⟩ := IsSemisimpleRing.ideal_eq_span_idempotent J
  have hJidem : IsIdempotentElem J := by
    rw [hJe]
    simp [IsIdempotentElem, Ideal.span_singleton_mul_span_singleton, heJ.eq]
  haveI hFE : Algebra.FormallyEtale B (B ⧸ J) := by
    refine (Algebra.FormallyEtale.iff_of_surjective (R := B) (S := B ⧸ J) ?_).mpr ?_
    · simpa [Ideal.Quotient.algebraMap_eq] using Ideal.Quotient.mk_surjective (I := J)
    · have hker : RingHom.ker (algebraMap B (B ⧸ J)) = J := by
        simpa [Ideal.Quotient.algebraMap_eq] using Ideal.mk_ker (I := J)
      rwa [hker]
  haveI hFEK : Algebra.FormallyEtale K (B ⧸ J) := Algebra.FormallyEtale.comp K B (B ⧸ J)
  haveI hFinC : Module.Finite K (B ⧸ J) := Module.Finite.quotient K J
  have hEtC : Algebra.Etale K (B ⧸ J) := by
    refine ⟨hFEK, ?_⟩
    exact (Algebra.FinitePresentation.of_finiteType (R := K)).mp inferInstance
  let crt : B ≃ₐ[K] ((B ⧸ I) × (B ⧸ J)) := algEquiv_prod_quotient_of_isCompl I J hJ
  let q : (B ⧸ I) ≃ₐ[K] A := Ideal.quotientKerAlgEquivOfSurjective hf
  let ee : B ≃ₐ[K] (A × (B ⧸ J)) :=
    crt.trans (AlgEquiv.prodCongr q (AlgEquiv.refl : (B ⧸ J) ≃ₐ[K] (B ⧸ J)))
  refine ⟨B ⧸ J, inferInstance, inferInstance, hFinC, hEtC, ee, ?_⟩
  have crt_apply : ∀ b : B, crt b = (Ideal.Quotient.mk I b, Ideal.Quotient.mk J b) :=
    algEquiv_prod_quotient_of_isCompl_apply I J hJ
  have ee_apply : ∀ b : B, ee b = (f b, Ideal.Quotient.mk J b) := by
    intro b
    change (AlgEquiv.prodCongr q (AlgEquiv.refl : (B ⧸ J) ≃ₐ[K] (B ⧸ J))) (crt b) = _
    rw [crt_apply]
    simp only [AlgEquiv.prodCongr_apply, Equiv.prodCongr_apply, Prod.map_apply]
    have hq : q (Ideal.Quotient.mk I b) = f b :=
      Ideal.quotientKerAlgEquivOfSurjective_mk hf b
    rw [hq]
  ext b
  change f b = (ee b).1
  rw [ee_apply]

end S1771
