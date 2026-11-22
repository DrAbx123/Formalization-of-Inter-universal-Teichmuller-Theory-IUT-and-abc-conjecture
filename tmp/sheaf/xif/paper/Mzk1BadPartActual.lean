/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import Mathlib.Data.Nat.MaxPowDiv
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic

/-! # A679 hull: the bad-prime part `N_bad` (distinct rational primes)

`qVFamTensorP T b` is the rational prime under the bad F-place of `b`.  Different
bad places can lie over the SAME rational prime (e.g. `F_mod = ℚ(i)`), so the naive
product over bad places can repeat a prime.  We define the bad prime support by the
DISTINCT rational primes and `badPart N = ∏_{p ∈ N.primeFactors ∩ support} p^{v_p(N)}`;
it divides `N` by the prime-factorization identity.

This is the corrected `N_bad` for mainline's `CorrectedRegionFormula`.
No canonical object changed. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1BadPartActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open scoped BigOperators

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The **distinct rational primes** supporting the bad places. -/
noncomputable def badPrimeSupport : Finset Nat :=
  Finset.univ.image (fun b : Bad (nativePlaceSelection T) => qVFamTensorP T b)

theorem mem_badPrimeSupport {p : Nat} :
    p ∈ badPrimeSupport T ↔ ∃ b : Bad (nativePlaceSelection T), qVFamTensorP T b = p := by
  unfold badPrimeSupport
  simp

theorem badPrimeSupport_prime {p : Nat} (hp : p ∈ badPrimeSupport T) : p.Prime := by
  rw [mem_badPrimeSupport] at hp
  obtain ⟨b, rfl⟩ := hp
  exact Fact.out

/-- `N_bad = ∏_{p ∈ N.primeFactors ∩ bad support} p^{v_p(N)}`. -/
noncomputable def badPart (N : Nat) : Nat :=
  ∏ p ∈ N.primeFactors.filter (fun p => p ∈ badPrimeSupport T),
    p ^ padicValNat p N

/-- **`N_bad ∣ N`**: a subproduct of the prime factorization of `N`. -/
theorem badPart_dvd {N : Nat} (hN : 0 < N) : badPart T N ∣ N := by
  have hN0 : N ≠ 0 := hN.ne'
  have hNprod : (∏ p ∈ N.primeFactors, p ^ padicValNat p N) = N := by
    have hcongr : (∏ p ∈ N.primeFactors, p ^ padicValNat p N) =
        ∏ p ∈ N.primeFactors, p ^ N.factorization p := by
      exact Finset.prod_congr rfl fun p hp => by
        rw [Nat.factorization_def N (Nat.prime_of_mem_primeFactors hp)]
    rw [hcongr]
    exact (Nat.prod_primeFactors_pow_factorization hN0).symm
  have hdvd : (∏ p ∈ N.primeFactors.filter
      (fun p => p ∈ badPrimeSupport T), p ^ padicValNat p N) ∣
      (∏ p ∈ N.primeFactors, p ^ padicValNat p N) :=
    Finset.prod_dvd_prod_of_subset (N.primeFactors.filter
      (fun p => p ∈ badPrimeSupport T)) N.primeFactors
      (fun p => p ^ padicValNat p N) (Finset.filter_subset _ _)
  rw [hNprod] at hdvd
  simpa [badPart] using hdvd

/-- **`N_bad ≤ N`** for positive `N`. -/
theorem badPart_le {N : Nat} (hN : 0 < N) : badPart T N ≤ N :=
  Nat.le_of_dvd hN (badPart_dvd T hN)

def badPartRows : List (String × String × String) :=
  [ ("bad prime support", "badPrimeSupport = image qVFamTensorP", "DEF (distinct rational primes)"),
    ("badPart", "badPart N = ∏ p^{v_p(N)} over N.primeFactors ∩ support", "DEF"),
    ("divisibility", "badPart_dvd", "PROVED"),
    ("boundedness", "badPart_le", "PROVED (N > 0)"),
    ("note", "naive product over bad places can repeat p (Fmod = Q(i))", "CORRECTION") ]

theorem badPartRows_length : badPartRows.length = 5 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1BadPartActual.badPart_dvd
#print axioms LeanFormal.IUT.XiFPaper.Mzk1BadPartActual.badPart_le

end LeanFormal.IUT.XiFPaper.Mzk1BadPartActual

end