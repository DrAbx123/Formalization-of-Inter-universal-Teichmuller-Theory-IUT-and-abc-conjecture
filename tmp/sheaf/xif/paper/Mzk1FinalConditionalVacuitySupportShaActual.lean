import LeanFormal.IUT.Foundations.Arithmetic.PrimitiveAdditive
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Tactic

/-! # FinalConditional vacuity support (lattice read-only companion)

The Lead A703 correction: for a fixed finite bad set `B`, the hypothesis `hfull`
that every prime of `N = a + b + c + 1` lies in `B` is unsatisfiable, because
`N` runs over all odd numbers `>= 5`.  This file proves the arithmetic core
generically; it does NOT modify the retracted chain.  The canonical machine
proof `Mzk1FinalConditionalVacuityActual` is owned by mainline. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1FinalConditionalVacuitySupportShaActual

open LeanFormal.IUT

/-- For every finite bad set there is a prime `p >= 5` outside it. -/
theorem exists_prime_ge_five_not_mem (B : Finset Nat) :
    exists p : Nat, 5 ≤ p ∧ p.Prime ∧ p ∉ B := by
  obtain ⟨p, hp_ge, hp_prime⟩ :=
    Nat.exists_infinite_primes (max 5 (B.sup id + 1))
  refine ⟨p, ?_, hp_prime, ?_⟩
  · exact le_trans (le_max_left 5 (B.sup id + 1)) hp_ge
  · intro hpB
    have hp_le : p ≤ B.sup id := Finset.le_sup (f := id) hpB
    have hb : B.sup id + 1 ≤ p :=
      le_trans (le_max_right 5 (B.sup id + 1)) hp_ge
    omega

/-- The `hfull` hypothesis is unsatisfiable for every finite bad set. -/
theorem hfull_unsatisfiable (B : Finset Nat) :
    ¬ (forall a b c : Nat, PrimitiveAdditiveTriple a b c →
      forall q : Nat, q ∈ (a + b + c + 1).primeFactors → q ∈ B) := by
  intro hfull
  obtain ⟨p, hp5, hpp, hpB⟩ := exists_prime_ge_five_not_mem B
  have hodd : Odd p := by
    rcases Nat.Prime.eq_two_or_odd' hpp with h2 | ho
    · omega
    · exact ho
  obtain ⟨k, hk⟩ := hodd
  subst hk
  have hk2 : 2 ≤ k := by omega
  have htriple : PrimitiveAdditiveTriple 1 (k - 1) k := by
    refine ⟨by norm_num, by omega, by omega, ?_⟩
    exact Nat.coprime_one_left _
  have hN : 1 + (k - 1) + k + 1 = 2 * k + 1 := by omega
  have hmem : 2 * k + 1 ∈ (2 * k + 1).primeFactors := by
    rw [Nat.mem_primeFactors]
    exact ⟨hpp, dvd_rfl, by omega⟩
  have hBmem : 2 * k + 1 ∈ B :=
    hfull 1 (k - 1) k htriple (2 * k + 1) (by rwa [hN])
  exact hpB hBmem

#print axioms hfull_unsatisfiable

end LeanFormal.IUT.XiFPaper.Mzk1FinalConditionalVacuitySupportShaActual
