/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1FinalConditionalABCActual
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Lattice.Lemmas
import Mathlib.Tactic

/-!
# A703 CORRECTION: `final_conditional_ABC` is RETRACTED / VACUOUS (mainline)

**The theorem `Mzk1FinalConditionalABCActual.final_conditional_ABC` is RETRACTED as
unsatisfiable**: its hypothesis `hfull` (for fixed `T`, the bad-prime support of
`N = a+b+c+1` is contained in the finite bad set of `T`) is UNSATISFIABLE.

Proof (`hfull_unsatisfiable`): take a prime `P >= 5` outside the finite bad set (exists
by infinitude of primes).  With `P = 2k+1`, `k >= 2`, the triple `(1, k-1, k)` is an
ABC triple and `N = 1 + (k-1) + k + 1 = P`.  `hfull` would give
`P = ∏_{b ∈ bad} p_b^{e_b}`.  Either some exponent is nonzero, then the prime `p_b`
divides `P`, so `p_b = P`, contradicting `p_b < P`; or all exponents are zero, giving
`P = 1`, contradiction.  Hence no `eN` satisfies `hfull`.

The `N = a+b+c+1` scaling is NOT the paper structure (paper bad primes = primes of
`abc`; weights normalized by `[F_v:Q_p]/[F:Q]`).  The `hfull`-based chain is kept as
history only.  No canonical change; ABC gate NOT passed. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1FinalConditionalVacuityActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- **Vacuity**: for fixed `T` there is no `eN` making the `hfull` hypothesis true. -/
theorem hfull_unsatisfiable
    (eN : Nat → Nat → Nat → Bad (nativePlaceSelection T) → Nat) :
    ¬ (∀ a b c : Nat, IsABCTriple a b c →
        a + b + c + 1 = ∏ bBad : Bad (nativePlaceSelection T),
          (qVFamTensorP T bBad) ^ (eN a b c bBad)) := by
  intro hfull
  -- a bound on all bad primes
  set B : Nat := Finset.univ.sup (fun bBad : Bad (nativePlaceSelection T) =>
    qVFamTensorP T bBad) with hB
  obtain ⟨P, hPge, hPprime⟩ := Nat.exists_infinite_primes (max (B + 1) 5)
  have hP5 : 5 ≤ P := le_trans (le_max_right _ _) hPge
  have hBlt : B < P := by
    have h1 : B + 1 ≤ P := le_trans (le_max_left _ _) hPge
    omega
  have hPodd : Odd P := hPprime.odd_of_ne_two (by omega)
  obtain ⟨k, hk⟩ := hPodd
  have hk2 : 2 ≤ k := by omega
  -- the ABC triple (1, k-1, k) with N = P
  have htriple : IsABCTriple 1 (k - 1) k :=
    ⟨Nat.one_pos, by omega, by omega, Nat.coprime_one_left _⟩
  have hN : 1 + (k - 1) + k + 1 = P := by omega
  have hprod : (∏ bBad : Bad (nativePlaceSelection T),
      (qVFamTensorP T bBad) ^ (eN 1 (k - 1) k bBad)) = P := by
    have h := hfull 1 (k - 1) k htriple
    rw [hN] at h
    exact h.symm
  by_cases hS : ∃ bBad : Bad (nativePlaceSelection T), eN 1 (k - 1) k bBad ≠ 0
  · obtain ⟨b0, hb0⟩ := hS
    have hprime : Nat.Prime (qVFamTensorP T b0) := Fact.out
    have hle : qVFamTensorP T b0 ≤ B := by
      rw [hB]
      exact Finset.le_sup (f := fun bBad : Bad (nativePlaceSelection T) =>
        qVFamTensorP T bBad) (Finset.mem_univ b0)
    have hdvd_pow : (qVFamTensorP T b0) ^ (eN 1 (k - 1) k b0) ∣
        (∏ bBad : Bad (nativePlaceSelection T),
          (qVFamTensorP T bBad) ^ (eN 1 (k - 1) k bBad)) :=
      Finset.dvd_prod_of_mem _ (Finset.mem_univ b0)
    have hdvd : qVFamTensorP T b0 ∣ P := by
      rw [← hprod]
      exact (dvd_pow_self _ hb0).trans hdvd_pow
    have hpeq : P = qVFamTensorP T b0 := by
      have hne1 : qVFamTensorP T b0 ≠ 1 := hprime.ne_one
      exact (hPprime.dvd_iff_eq hne1).mp hdvd
    have hlt : qVFamTensorP T b0 < P := lt_of_le_of_lt hle hBlt
    omega
  · push_neg at hS
    have h1 : (∏ bBad : Bad (nativePlaceSelection T),
        (qVFamTensorP T bBad) ^ (eN 1 (k - 1) k bBad)) = 1 := by
      apply Finset.prod_eq_one
      intro bBad _
      rw [hS bBad]
      simp
    rw [h1] at hprod
    omega

/-- Statement-level retraction: the `final_conditional_ABC` hypothesis package is
  unsatisfiable for every `eN`. -/
theorem final_conditional_ABC_retracted
    (eN : Nat → Nat → Nat → Bad (nativePlaceSelection T) → Nat) :
    ¬ (∀ a b c : Nat, IsABCTriple a b c →
        a + b + c + 1 = ∏ bBad : Bad (nativePlaceSelection T),
          (qVFamTensorP T bBad) ^ (eN a b c bBad)) :=
  hfull_unsatisfiable T eN

/-- Audit rows of the correction. -/
def vacuityRows : List (String × String) :=
  [ ("final_conditional_ABC", "RETRACTED: hfull unsatisfiable (hfull_unsatisfiable)"),
    ("bad set for fixed T", "finite; N=2k+1 hits new primes infinitely often"),
    ("N = a+b+c+1 scaling", "NOT the paper structure (paper: bad primes = primes of abc)"),
    ("paper correction", "triple-dependent Theta-data; normalized weight d_b"),
    ("scope", "history only; ABC gate NOT passed; no canonical change") ]

theorem vacuityRows_length : vacuityRows.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1FinalConditionalVacuityActual

end

/-! ### Axiom gates (top level) -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1FinalConditionalVacuityActual.hfull_unsatisfiable
#print axioms LeanFormal.IUT.XiFPaper.Mzk1FinalConditionalVacuityActual.final_conditional_ABC_retracted
#print axioms LeanFormal.IUT.XiFPaper.Mzk1FinalConditionalVacuityActual.vacuityRows_length