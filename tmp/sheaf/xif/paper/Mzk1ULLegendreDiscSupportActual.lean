/- U-C: Legendre discriminant prime support (the support-inclusion content of hcond).

E_lam: y^2 = x (x-1) (x-lam) has discriminant 16 lam^2 (1-lam)^2, hence any prime
of bad reduction divides 16 lam^2 (1-lam)^2, i.e. every bad prime is 2 or divides
lam or 1-lam (paper/route: Legendre discriminant => bad primes subset of the
lam/1-lam bad primes plus the 2-adic place).  This file proves the elementary
integer statement that feeds david's `LegendreSupportIncl.tpd_subset` shape
(the arithmetic identification of 'bad prime' with 'divides the discriminant'
is the curve-side obligation; here we prove the discriminant-prime support).
-/
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

namespace LeanFormal.IUT.XiFPaper.Mzk1ULLegendreDiscSupportActual

/-- PROVED: every prime factor of 16 lam^2 (lam-1)^2 is 2 or divides lam or lam-1. -/
theorem legendre_disc_primeFactors_subset (lam : ℕ) (h2 : 2 ≤ lam) :
    (16 * lam ^ 2 * (lam - 1) ^ 2).primeFactors ⊆ lam.primeFactors ∪ (lam - 1).primeFactors ∪ {2} :=
  by
  intro p hp
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hp_dvd : p ∣ 16 * lam ^ 2 * (lam - 1) ^ 2 := Nat.dvd_of_mem_primeFactors hp
  have hlam0 : lam ≠ 0 := by omega
  have hlam1 : lam - 1 ≠ 0 := by omega
  have hcases : p = 2 ∨ p ∈ lam.primeFactors ∨ p ∈ (lam - 1).primeFactors := by
    rcases hp_prime.dvd_mul.mp hp_dvd with hleft | hright
    · rcases hp_prime.dvd_mul.mp hleft with h16 | hlam2
      · left
        have h16' : p ∣ 2 ^ 4 := by norm_num at h16 ⊢; exact h16
        exact (Nat.prime_dvd_prime_iff_eq hp_prime Nat.prime_two).mp
          (hp_prime.dvd_of_dvd_pow h16')
      · right; left
        exact Nat.mem_primeFactors.mpr ⟨hp_prime, hp_prime.dvd_of_dvd_pow hlam2, hlam0⟩
    · right; right
      exact Nat.mem_primeFactors.mpr ⟨hp_prime, hp_prime.dvd_of_dvd_pow hright, hlam1⟩
  rcases hcases with rfl | h | h
  · simp
  · simp [h]
  · simp [h]

end LeanFormal.IUT.XiFPaper.Mzk1ULLegendreDiscSupportActual
