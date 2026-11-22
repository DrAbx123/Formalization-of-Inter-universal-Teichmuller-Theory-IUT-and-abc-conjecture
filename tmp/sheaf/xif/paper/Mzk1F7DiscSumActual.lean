import tmp.sheaf.xif.paper.Mzk1F7DiscLocalGlobalActual
import tmp.sheaf.xif.paper.Mzk1F7DiscProductActual
import tmp.sheaf.xif.paper.Mzk1F7DiscPrimeFactorActual
import Mathlib.Tactic
/-!
# F7 local-global different dictionary (route §8.5), sum layer

`v_p(|disc K|) = Σ_{P} v_P(𝔇) · [p = under(P)] · f(P)` as a multiset sum over the
normalized factors of the different ideal. This is the main local-global formula
feeding `differentContribution K p ≤ log p` in the tame case.

Lead lane: H-T / P8-P.
-/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1F7DiscSumActual

open Module Ideal UniqueFactorizationMonoid NumberField IsDedekindDomain
open LeanFormal.IUT.XiFPaper.Mzk1F7DiscLocalGlobalActual
open LeanFormal.IUT.XiFPaper.Mzk1F7DiscProductActual
open LeanFormal.IUT.XiFPaper.Mzk1F7DiscPrimeFactorActual

variable {K : Type*} [Field K] [NumberField K]
variable {p : ℕ} [Fact p.Prime]

/-- Route §8.5 local-global: the `p`-adic exponent of `|disc K|` is the multiset sum
over the normalized factors of the different ideal of `f(P)` when `P` lies over `p`. -/
theorem disc_factorization_eq_multiset_sum :
    (NumberField.discr K).natAbs.factorization p =
      ((normalizedFactors (differentIdeal ℤ (𝓞 K))).map
        (fun P => (if Ideal.absNorm (Ideal.under ℤ P) = p then P.inertiaDeg ℤ else 0))).sum := by
  rw [← absNorm_differentIdeal_eq_discr]
  rw [absNorm_differentIdeal_eq_multiset_prod]
  rw [factorization_multiset_prod_absNorm (normalizedFactors (differentIdeal ℤ (𝓞 K)))
    (fun P hP => (prime_of_normalized_factor P hP).ne_zero)]
  congr 1
  refine Multiset.map_congr rfl ?_
  intro P hP
  have hprime : Prime P := prime_of_normalized_factor P hP
  have hne : P ≠ ⊥ := hprime.ne_zero
  haveI : P.IsPrime := (Ideal.prime_iff_isPrime hne).mp hprime
  exact factorization_absNorm_eq_ite P hne

end LeanFormal.IUT.XiFPaper.Mzk1F7DiscSumActual
