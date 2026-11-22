/- H-T 8.2 (batch4d): log-product to sum over the normalized factors of the relative
different, the different exponent delta(P) = count of P, and the old/new inertia degree bridge. -/
import tmp.sheaf.xif.paper.Mzk1G1RelativeDifferentFactorizationActual
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1RelativeDifferentLogActual

open NumberField
open UniqueFactorizationMonoid
open LeanFormal.IUT.XiFPaper.Mzk1G1RelativeDifferentFactorizationActual

universe u

section

variable {K : Type u} [Field K] [NumberField K]
variable {L : Type u} [Field L] [NumberField L] [Algebra K L]
variable [Module.Finite (𝓞 K) (𝓞 L)]

/-- The different exponent delta(P): the multiplicity of the prime P in the relative different. -/
def differentExponent (P : Ideal (𝓞 L)) : ℕ :=
  (normalizedFactors (differentIdeal (𝓞 K) (𝓞 L))).count P

/-- log of the different norm is the sum of the logs of the normalized-factor norms. -/
theorem log_absNorm_differentIdeal_eq_sum :
    Real.log ((Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 L)) : ℕ) : ℝ) =
      ((normalizedFactors (differentIdeal (𝓞 K) (𝓞 L))).map
        (fun P => Real.log ((Ideal.absNorm P : ℕ) : ℝ))).sum := by
  have hI : differentIdeal (𝓞 K) (𝓞 L) ≠ ⊥ := differentIdeal_ne_bot
  have hne : ∀ P ∈ normalizedFactors (differentIdeal (𝓞 K) (𝓞 L)),
      ((Ideal.absNorm P : ℕ) : ℝ) ≠ 0 := by
    intro P hP
    have hprime : P.IsPrime := ((Ideal.mem_normalizedFactors_iff hI).mp hP).1
    have hPne : P ≠ ⊥ := by
      intro hbot
      have hle : differentIdeal (𝓞 K) (𝓞 L) ≤ P := ((Ideal.mem_normalizedFactors_iff hI).mp hP).2
      rw [hbot] at hle
      exact hI (le_bot_iff.mp hle)
    have : Ideal.absNorm P ≠ 0 := by
      intro h0
      exact hPne (Ideal.absNorm_eq_zero_iff.mp h0)
    exact Nat.cast_ne_zero.mpr this
  rw [absNorm_differentIdeal_eq_prod, Nat.cast_multiset_prod, Multiset.map_map]
  rw [Real.log_multiset_prod]
  · simp [Multiset.map_map, Function.comp_def]
  · intro x hx
    obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.mp hx
    exact hne P hP

/-- log of the different norm as a Finset sum over the support with multiplicities. -/
theorem log_absNorm_differentIdeal_eq_finset_sum :
    Real.log ((Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 L)) : ℕ) : ℝ) =
      ∑ P ∈ (normalizedFactors (differentIdeal (𝓞 K) (𝓞 L))).toFinset,
        (normalizedFactors (differentIdeal (𝓞 K) (𝓞 L))).count P •
          Real.log ((Ideal.absNorm P : ℕ) : ℝ) := by
  classical
  rw [log_absNorm_differentIdeal_eq_sum, Finset.sum_multiset_map_count]

/-- log of the different norm as a Finset sum with the different exponents delta(P). -/
theorem log_absNorm_differentIdeal_eq_finset_sum_delta :
    Real.log ((Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 L)) : ℕ) : ℝ) =
      ∑ P ∈ (normalizedFactors (differentIdeal (𝓞 K) (𝓞 L))).toFinset,
        (differentExponent (K := K) (L := L) P : ℝ) *
          Real.log ((Ideal.absNorm P : ℕ) : ℝ) := by
  classical
  rw [log_absNorm_differentIdeal_eq_finset_sum]
  apply Finset.sum_congr rfl
  intro P _
  rw [differentExponent, nsmul_eq_mul]

/-- The absolute norm of a prime ideal is absNorm(P.under) to the (new-style) inertia degree. -/
theorem absNorm_prime_eq_pow_inertiaDeg_new (P : Ideal (𝓞 L)) [P.IsPrime] (hP : P ≠ ⊥) :
    Ideal.absNorm P = Ideal.absNorm (P.under (𝓞 K)) ^ P.inertiaDeg (𝓞 K) := by
  have hp_ne_bot : P.under (𝓞 K) ≠ ⊥ := by
    intro h
    haveI : P.LiesOver (⊥ : Ideal (𝓞 K)) := ⟨h.symm⟩
    exact hP (Ideal.eq_bot_of_liesOver_bot (A := 𝓞 K) P)
  exact (Ideal.absNorm_pow_inertiaDeg (p := P.under (𝓞 K)) (q := P) (R := 𝓞 K)).symm

/-- Bridge between the old-style inertiaDeg' and the new-style inertiaDeg. -/
theorem inertiaDeg'_eq_inertiaDeg_under (P : Ideal (𝓞 L)) [P.IsPrime] (hP : P ≠ ⊥) :
    (P.under (𝓞 K)).inertiaDeg' P = P.inertiaDeg (𝓞 K) := by
  have hp_ne_bot : P.under (𝓞 K) ≠ ⊥ := by
    intro h
    haveI : P.LiesOver (⊥ : Ideal (𝓞 K)) := ⟨h.symm⟩
    exact hP (Ideal.eq_bot_of_liesOver_bot (A := 𝓞 K) P)
  haveI : (P.under (𝓞 K)).IsMaximal := Ideal.isMaximal_of_isPrime_of_ne_bot _ hp_ne_bot
  haveI : P.IsMaximal := Ideal.isMaximal_of_isPrime_of_ne_bot _ hP
  exact Ideal.inertiaDeg'_eq_inertiaDeg (p := P.under (𝓞 K)) (q := P) (R := 𝓞 K)

end

#print axioms log_absNorm_differentIdeal_eq_sum
#print axioms log_absNorm_differentIdeal_eq_finset_sum_delta
#print axioms absNorm_prime_eq_pow_inertiaDeg_new
#print axioms inertiaDeg'_eq_inertiaDeg_under
end LeanFormal.IUT.XiFPaper.Mzk1G1RelativeDifferentLogActual
