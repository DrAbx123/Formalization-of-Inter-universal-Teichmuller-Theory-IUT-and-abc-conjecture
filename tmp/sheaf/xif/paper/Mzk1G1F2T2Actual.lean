/- Route 8.2 T2: the relative different exponent lower bound in terms of the ramification
index.  For K subset L number fields, p a maximal ideal of O_K and P a prime of O_L over p,
P.ramificationIdx(O_K) - 1 is at most the multiplicity of P in the relative different. -/
import tmp.sheaf.xif.paper.Mzk1G1F7DifferentExponentBoundsActual
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1F2T2Actual

open NumberField
open UniqueFactorizationMonoid
universe u

section

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [Module.Finite (𝓞 K) (𝓞 L)]

/-- **T2 (generic)**: the ramification index minus one is bounded by the relative-different
multiplicity. -/
theorem T2_relative_different_count (p : Ideal (𝓞 K)) [p.IsMaximal] (hp : p ≠ ⊥)
    (P : Ideal (𝓞 L)) [P.IsPrime] (hP : P.LiesOver p) :
    P.ramificationIdx (𝓞 K) - 1 ≤
      (normalizedFactors (differentIdeal (𝓞 K) (𝓞 L))).count P := by
  classical
  have hPmem : P ∈ p.primesOver (𝓞 L) := ⟨‹P.IsPrime›, hP⟩
  have hPne : P ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver hp hPmem
  haveI : Algebra.IsIntegral (𝓞 K) (𝓞 L) := IsIntegralClosure.isIntegral_algebra (𝓞 K) L
  -- factorization of p in O_L: p * O_L = prod P^e
  have hfac := Ideal.map_algebraMap_eq_finsetProd_pow (S := 𝓞 K) (R := 𝓞 L) (p := p) hp
  -- P^e divides the product, hence p * O_L
  have hmemF : P ∈ (p.primesOver (𝓞 L)).toFinset := by
    rw [Set.mem_toFinset]
    exact hPmem
  have hdiv : P ^ P.ramificationIdx (𝓞 K) ∣
      ∏ Q ∈ (p.primesOver (𝓞 L)).toFinset, Q ^ Q.ramificationIdx (𝓞 K) :=
    Finset.dvd_prod_of_mem _ hmemF
  rw [← hfac] at hdiv
  -- Mathlib: P^e | p*B implies P^(e-1) | differentIdeal
  have he : P.ramificationIdx (𝓞 K) ≠ 0 :=
    (Ideal.ramificationIdx_pos P (𝓞 K)).ne'
  have hpow : P ^ (P.ramificationIdx (𝓞 K) - 1) ∣ differentIdeal (𝓞 K) (𝓞 L) :=
    pow_sub_one_dvd_differentIdeal_aux (A := 𝓞 K) (K := K) (B := 𝓞 L) (L := L) P he hp hdiv
  have hcount :=
    LeanFormal.IUT.XiFPaper.Mzk1G1F7DifferentExponentBoundsActual.count_differentIdeal_ge_ramification_sub_one
      (K := K) (L := L) P hPne hpow
  exact hcount

end

#print axioms T2_relative_different_count
end LeanFormal.IUT.XiFPaper.Mzk1G1F2T2Actual
