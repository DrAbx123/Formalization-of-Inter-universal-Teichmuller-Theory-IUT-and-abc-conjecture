/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.Tactic

/-! # Mzk1HViiiDictActual — (b) local-global dictionary: log-discriminant and log-conductor (A786)

Part (b) of the h_V property-(iii) assembly: the local sums `Sum d_p log p` and
`Sum delta_p log p` are identified with the log of the (absolute norm of the)
different ideal and with the log of an arithmetic conductor integer.

Proved here (pure Mathlib arithmetic + Mathlib's actual different ideal):
* `log_natCast_eq_sum_factorization`: for any `n != 0`,
  `log n = Sum_{p | n} v_p(n) * log p`;
* `diffLogSum_eq_log_abs_discr` and `diffLogSum_eq_log_absNorm_differentIdeal`:
  the different/discriminant log-sum equals `log |disc K|` and `log |N(differentIdeal)|`
  via Mathlib's `NumberField.absNorm_differentIdeal`;
* `condLogSum_eq_log_n`: the conductor log-sum `Sum delta_p log p` equals `log n` for
  the arithmetic integer `n` (the paper's conductor `f` is the remaining identification).

Gaps are listed in `hvIiiDictRows`.

-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.Mzk1HViiiDictActual

open NumberField
open scoped BigOperators

/-! ### A. The general log-factorization identity -/

/-- For `n != 0`: `log n = Sum_{p | n} v_p(n) * log p`. -/
theorem log_natCast_eq_sum_factorization (n : Nat) (hn : n ≠ 0) :
    Real.log (n : Real) =
      (n.primeFactors.sum (fun p => (n.factorization p : Real) * Real.log (p : Real))) := by
  have hmain : ((n : Real)) = ∏ p ∈ n.primeFactors, (p : Real) ^ n.factorization p := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn]
    rw [show ((n.factorization.prod (fun p e => p ^ e) : Nat) : Real) =
        (n.factorization.prod (fun p e => ((p : Real) ^ e))) by
      rw [Nat.cast_finsuppProd]
      simp only [Nat.cast_pow]]
    rw [Nat.prod_factorization_eq_prod_primeFactors (fun p e => ((p : Real) ^ e))]
  have hne : ∀ p ∈ n.primeFactors, ((p : Real) ^ n.factorization p) ≠ 0 := by
    intro p hp
    have hp0 : p ≠ 0 := (Nat.prime_of_mem_primeFactors hp).ne_zero
    exact pow_ne_zero _ (Nat.cast_ne_zero.mpr hp0)
  calc Real.log (n : Real)
      = Real.log (∏ p ∈ n.primeFactors, (p : Real) ^ n.factorization p) := by
          rw [hmain]
    _ = (n.primeFactors.sum (fun p => Real.log ((p : Real) ^ n.factorization p))) := by
          rw [Real.log_prod (fun p hp => hne p hp)]
    _ = (n.primeFactors.sum (fun p => (n.factorization p : Real) * Real.log (p : Real))) := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [Real.log_pow]

/-! ### B. The discriminant/different dictionary -/

/-- The local different log-sum attached to a number field: `Sum_{p | |disc K|} v_p(|disc K|) log p`. -/
noncomputable def diffLogSum (K : Type*) [Field K] [NumberField K] : Real :=
  (NumberField.discr K).natAbs.primeFactors.sum
    (fun p => ((NumberField.discr K).natAbs.factorization p : Real) * Real.log (p : Real))

/-- The different log-sum equals `log |disc K|`. -/
theorem diffLogSum_eq_log_abs_discr (K : Type*) [Field K] [NumberField K]
    (h : (NumberField.discr K).natAbs ≠ 0) :
    diffLogSum K = Real.log ((NumberField.discr K).natAbs : Real) :=
  (log_natCast_eq_sum_factorization (NumberField.discr K).natAbs h).symm

/-- The different log-sum equals `log |N(differentIdeal)|` (Mathlib's actual different ideal). -/
theorem diffLogSum_eq_log_absNorm_differentIdeal (K : Type*) [Field K] [NumberField K]
    (h : (NumberField.discr K).natAbs ≠ 0) :
    diffLogSum K = Real.log (((differentIdeal ℤ (𝓞 K)).absNorm : Nat) : Real) := by
  rw [diffLogSum_eq_log_abs_discr K h, NumberField.absNorm_differentIdeal (K := K)]

/-! ### C. The conductor log-sum -/

/-- The arithmetic conductor log-sum: `Sum_{p | n} v_p(n) log p`. -/
noncomputable def condLogSum (n : Nat) : Real :=
  n.primeFactors.sum (fun p => (n.factorization p : Real) * Real.log (p : Real))

/-- The conductor log-sum equals `log n`. -/
theorem condLogSum_eq_log_n (n : Nat) (hn : n ≠ 0) :
    condLogSum n = Real.log (n : Real) := by
  unfold condLogSum
  exact (log_natCast_eq_sum_factorization n hn).symm

/-! ### D. Status rows -/

def hvIiiDictRows : List (String × String) :=
  [ ("general log factorization log n = Sum v_p(n) log p", "PROVED"),
    ("diffSum = log |disc K|", "PROVED (diffLogSum_eq_log_abs_discr)"),
    ("diffSum = log |N(differentIdeal)|", "PROVED (Mathlib absNorm_differentIdeal)"),
    ("paper local definition Sum_p d_p log p = diffLogSum", "INPUT (identity of local different sums)"),
    ("condSum = log f (paper conductor)", "PARTIAL: condLogSum n = log n proved; identification n = conductor MISSING"),
    ("arithmeticWeight = Sum_{p | rad} log p (radical, v_p = 1)", "GREEN elsewhere (RationalPrimeSupport)") ]

theorem hvIiiDictRows_length : hvIiiDictRows.length = 6 := rfl

#check log_natCast_eq_sum_factorization
#check diffLogSum_eq_log_abs_discr
#check diffLogSum_eq_log_absNorm_differentIdeal
#check condLogSum_eq_log_n
#check hvIiiDictRows_length

end LeanFormal.IUT.XiFPaper.Mzk1HViiiDictActual
end
