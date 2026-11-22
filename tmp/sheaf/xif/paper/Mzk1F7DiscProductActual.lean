import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic
/-!
# F7 local-global different dictionary (route §8.5), product layer

The `p`-adic factorization of the norm of a product of nonzero ideals is the sum
of the factorizations of the factors. Combined with
`Ideal.prod_normalizedFactors_eq_self` this gives the `p`-adic factorization of
`absNorm (𝔇_{𝓞 K/ℤ}) = |disc K|` as a multiset sum over the normalized factors.

Lead lane: H-T / P8-P.
-/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1F7DiscProductActual

open Module Ideal UniqueFactorizationMonoid NumberField IsDedekindDomain

variable {K : Type*} [Field K] [NumberField K]
variable {p : ℕ} [Fact p.Prime]

theorem absNorm_ne_zero_of_ne_bot {P : Ideal (𝓞 K)} (hP : P ≠ ⊥) : Ideal.absNorm P ≠ 0 := by
  intro h
  rw [Ideal.absNorm_eq_zero_iff] at h
  exact hP h

theorem multiset_prod_absNorm_ne_zero (s : Multiset (Ideal (𝓞 K)))
    (hs : ∀ P ∈ s, P ≠ ⊥) : (s.map Ideal.absNorm).prod ≠ 0 := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a t ih =>
      rw [Multiset.map_cons, Multiset.prod_cons]
      exact mul_ne_zero (absNorm_ne_zero_of_ne_bot (hs a (Multiset.mem_cons_self ..)))
        (ih (fun P hP => hs P (Multiset.mem_cons_of_mem hP)))

/-- `p`-adic factorization of the norm of a product of nonzero ideals. -/
theorem factorization_multiset_prod_absNorm (s : Multiset (Ideal (𝓞 K)))
    (hs : ∀ P ∈ s, P ≠ ⊥) :
    ((s.map Ideal.absNorm).prod).factorization p =
      (s.map (fun P => (Ideal.absNorm P).factorization p)).sum := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a t ih =>
      have ha : Ideal.absNorm a ≠ 0 := absNorm_ne_zero_of_ne_bot (hs a (Multiset.mem_cons_self ..))
      have ht : (t.map Ideal.absNorm).prod ≠ 0 :=
        multiset_prod_absNorm_ne_zero t (fun P hP => hs P (Multiset.mem_cons_of_mem hP))
      rw [Multiset.map_cons, Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons,
        ← ih (fun P hP => hs P (Multiset.mem_cons_of_mem hP))]
      have hfac : ((Ideal.absNorm a * (t.map Ideal.absNorm).prod).factorization) p =
          (Ideal.absNorm a).factorization p + ((t.map Ideal.absNorm).prod).factorization p :=
        congrArg (fun f : ℕ →₀ ℕ => f p) (Nat.factorization_mul ha ht)
      exact hfac

end LeanFormal.IUT.XiFPaper.Mzk1F7DiscProductActual
