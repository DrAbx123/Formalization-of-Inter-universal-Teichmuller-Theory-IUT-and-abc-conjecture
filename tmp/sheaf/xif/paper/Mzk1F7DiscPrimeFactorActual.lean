import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.Ideal.Int
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic
/-!
# F7 local-global different dictionary (route §8.5), per-prime layer

For a prime ideal `P` of `𝓞 K`:
* `absNorm P = (absNorm (under ℤ P)) ^ inertiaDeg` (Mathlib
  `Ideal.absNorm_pow_inertiaDeg`);
* since the rational prime under `P` is a prime number, the `p`-adic
  factorization of `absNorm P` is `inertiaDeg` if `p` is that prime,
  and `0` otherwise.

These are the per-prime inputs of `v_p(|disc K|) = Σ_{P|p} v_P(𝔇)·f_P`.

Lead lane: H-T / P8-P.
-/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1F7DiscPrimeFactorActual

open Module Ideal UniqueFactorizationMonoid NumberField IsDedekindDomain

variable {K : Type*} [Field K] [NumberField K]
variable {p : ℕ} [Fact p.Prime]

/-- Absolute norm of a prime ideal over ℤ in terms of its rational norm and inertia degree. -/
theorem absNorm_eq_under_pow_inertiaDeg (P : Ideal (𝓞 K)) [P.IsPrime] :
    Ideal.absNorm P =
      (Ideal.absNorm (Ideal.under ℤ P)) ^ P.inertiaDeg ℤ := by
  haveI : P.LiesOver (Ideal.under ℤ P) := inferInstance
  exact (Ideal.absNorm_pow_inertiaDeg (R := ℤ) (S := 𝓞 K)
    (p := Ideal.under ℤ P) (q := P)).symm

/-- The `p`-adic exponent of `absNorm P` is `inertiaDeg` when the rational prime
under `P` is `p` and `0` otherwise. -/
theorem factorization_absNorm_eq_ite (P : Ideal (𝓞 K)) [P.IsPrime] (hP : P ≠ ⊥) :
    (Ideal.absNorm P).factorization p =
      if Ideal.absNorm (Ideal.under ℤ P) = p then P.inertiaDeg ℤ else 0 := by
  haveI : NeZero P := ⟨hP⟩
  have hq : (Ideal.absNorm (Ideal.under ℤ P)).Prime := Nat.absNorm_under_prime P
  rw [absNorm_eq_under_pow_inertiaDeg (K := K) P, Nat.Prime.factorization_pow hq]
  by_cases h : Ideal.absNorm (Ideal.under ℤ P) = p
  · simp [h]
  · simp [h, Ne.symm h]

end LeanFormal.IUT.XiFPaper.Mzk1F7DiscPrimeFactorActual
