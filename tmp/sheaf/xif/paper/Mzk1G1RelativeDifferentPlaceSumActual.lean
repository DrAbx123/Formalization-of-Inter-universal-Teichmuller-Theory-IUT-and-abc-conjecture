/- H-T 8.2 (batch4e, de-conditionalization step): replace the relative-different log term by
its place/inertia-degree form.  For a prime P of O_L the log of absNorm P is inertiaDeg times
the log of absNorm of the K-place below it, so the different norm sum becomes a sum of
delta(P) * f_{P/K} * log Nv terms (the shape used by the F2 different term). -/
import tmp.sheaf.xif.paper.Mzk1G1RelativeDifferentLogActual
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1RelativeDifferentPlaceSumActual

open NumberField
open UniqueFactorizationMonoid
open LeanFormal.IUT.XiFPaper.Mzk1G1RelativeDifferentLogActual
open LeanFormal.IUT.XiFPaper.Mzk1G1RelativeDifferentFactorizationActual

universe u

section

variable {K : Type u} [Field K] [NumberField K]
variable {L : Type u} [Field L] [NumberField L] [Algebra K L]
variable [Module.Finite (𝓞 K) (𝓞 L)]

/-- Unconditional form of the prime-norm logarithm:
log |N(P)| = f_{P/K} * log |N(p)| for a prime P over p = P.under. -/
theorem log_absNorm_prime_eq_inertiaDeg_mul_log (P : Ideal (𝓞 L)) [P.IsPrime] (hP : P ≠ ⊥) :
    Real.log ((Ideal.absNorm P : ℕ) : ℝ) =
      (P.inertiaDeg (𝓞 K) : ℝ) *
        Real.log ((Ideal.absNorm (P.under (𝓞 K)) : ℕ) : ℝ) := by
  have h := absNorm_prime_eq_pow_inertiaDeg_new (K := K) (L := L) P hP
  have hcast : ((Ideal.absNorm P : ℕ) : ℝ) =
      (((Ideal.absNorm (P.under (𝓞 K)) : ℕ) : ℝ)) ^ P.inertiaDeg (𝓞 K) := by
    rw [h]
    push_cast
    ring
  rw [hcast, Real.log_pow]

/-- The different norm logarithm in place/inertia-degree form:
log |N(different(O_K,O_L))| = sum_P delta(P) * f_{P/K} * log |N(under P)|. -/
theorem log_absNorm_differentIdeal_eq_finset_sum_inertiaDeg :
    Real.log ((Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 L)) : ℕ) : ℝ) =
      ∑ P ∈ (normalizedFactors (differentIdeal (𝓞 K) (𝓞 L))).toFinset,
        (differentExponent (K := K) (L := L) P : ℝ) *
          ((P.inertiaDeg (𝓞 K) : ℝ) *
            Real.log ((Ideal.absNorm (P.under (𝓞 K)) : ℕ) : ℝ)) := by
  classical
  rw [log_absNorm_differentIdeal_eq_finset_sum_delta]
  apply Finset.sum_congr rfl
  intro P hPmem
  have hI : differentIdeal (𝓞 K) (𝓞 L) ≠ ⊥ := differentIdeal_ne_bot
  have hnf : P ∈ normalizedFactors (differentIdeal (𝓞 K) (𝓞 L)) :=
    Multiset.mem_toFinset.mp hPmem
  have hprime : P.IsPrime := ((Ideal.mem_normalizedFactors_iff hI).mp hnf).1
  have hPne : P ≠ ⊥ := by
    intro hbot
    have hle : differentIdeal (𝓞 K) (𝓞 L) ≤ P := ((Ideal.mem_normalizedFactors_iff hI).mp hnf).2
    rw [hbot] at hle
    exact hI (le_bot_iff.mp hle)
  haveI := hprime
  rw [log_absNorm_prime_eq_inertiaDeg_mul_log (K := K) (L := L) (P := P) hPne]

end

#print axioms log_absNorm_prime_eq_inertiaDeg_mul_log
#print axioms log_absNorm_differentIdeal_eq_finset_sum_inertiaDeg
end LeanFormal.IUT.XiFPaper.Mzk1G1RelativeDifferentPlaceSumActual
