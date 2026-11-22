/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.IUTII.Kummer.SourceLogShellCarrier

/-!
# IUT-II log-shell carrier: arithmetic of p and p* (Kummer node addendum)

Declaration-level addendum to `SourceLogShellCarrier`: the log-shell scale
`p* = p` (p odd) / `p* = p^2` (p even) is a divisor of p^2, equals p or p^2,
and divides the carrier prime; these elementary facts are used in the
`(p*)^{-1}`-normalization of the log-shell and in the p-adic scaling bookkeeping.

SHEAF node: iuti-ii:Kummer.LogShellCarrierArithmetic (kind theorem, status
PENDING-VERIFY until the DAG watchdog reports EXIT0).  No new axioms.
-/

namespace LeanFormal.IUT

/-- Odd primes are their own log-shell scale. -/
theorem sourceLogShellStar_odd (p : Nat) (hp : p % 2 = 1) :
    sourceLogShellStar p = p := by
  simp [sourceLogShellStar, hp]

/-- Even primes are squared in the log-shell scale. -/
theorem sourceLogShellStar_even (p : Nat) (hp : p % 2 ≠ 1) :
    sourceLogShellStar p = p * p := by
  simp [sourceLogShellStar, hp]

/-- The log-shell scale is either the prime or its square. -/
theorem sourceLogShellStar_self_or_sq (p : Nat) :
    sourceLogShellStar p = p ∨ sourceLogShellStar p = p * p := by
  by_cases hp : p % 2 = 1
  · exact Or.inl (sourceLogShellStar_odd p hp)
  · exact Or.inr (sourceLogShellStar_even p hp)

/-- The prime divides its log-shell scale. -/
theorem sourceLogShellStar_dvd (p : Nat) : p ∣ sourceLogShellStar p := by
  by_cases hp : p % 2 = 1
  · rw [sourceLogShellStar_odd p hp]
  · rw [sourceLogShellStar_even p hp]
    exact dvd_mul_right p p

/-- The carrier prime divides its log-shell scale p*. -/
theorem SourceLogShellDatum.pStar_dvd (D : SourceLogShellDatum) :
    D.p ∣ D.pStar := by
  exact sourceLogShellStar_dvd D.p

/-- The log-shell scale p* is the prime or its square. -/
theorem SourceLogShellDatum.pStar_self_or_sq (D : SourceLogShellDatum) :
    D.pStar = D.p ∨ D.pStar = D.p * D.p := by
  exact sourceLogShellStar_self_or_sq D.p

/-- The log-shell scale is nonzero for a positive prime. -/
theorem sourceLogShellStar_ne_zero {p : Nat} (hp : 0 < p) :
    sourceLogShellStar p ≠ 0 := by
  exact ne_of_gt (sourceLogShellStar_pos hp)

/-- The log-shell scale divides the square of the prime. -/
theorem sourceLogShellStar_dvd_sq (p : Nat) : sourceLogShellStar p ∣ p * p := by
  by_cases hp : p % 2 = 1
  · rw [sourceLogShellStar_odd p hp]
    exact dvd_mul_right p p
  · rw [sourceLogShellStar_even p hp]

/-- p* divides the square of the carrier prime. -/
theorem SourceLogShellDatum.pStar_dvd_sq (D : SourceLogShellDatum) :
    D.pStar ∣ D.p * D.p := by
  exact sourceLogShellStar_dvd_sq D.p

/-- For a positive carrier prime, p* is nonzero. -/
theorem SourceLogShellDatum.pStar_ne_zero' (D : SourceLogShellDatum)
    (hp : 0 < D.p) : D.pStar ≠ 0 := by
  exact sourceLogShellStar_ne_zero hp

/-- The log-shell scale is the first or the second power of the prime. -/
theorem sourceLogShellStar_eq_pow (p : Nat) :
    sourceLogShellStar p = p ^ 1 ∨ sourceLogShellStar p = p ^ 2 := by
  rcases sourceLogShellStar_self_or_sq p with h | h
  · exact Or.inl (by simpa using h)
  · exact Or.inr (by simpa [pow_two] using h)

/-- For a positive prime the log-shell scale is positive. -/
theorem sourceLogShellStar_pos' {p : Nat} (hp : 0 < p) :
    0 < sourceLogShellStar p := sourceLogShellStar_pos hp

/-- For a positive carrier prime, p* is positive. -/
theorem SourceLogShellDatum.pStar_pos' (D : SourceLogShellDatum) (hp : 0 < D.p) :
    0 < D.pStar := sourceLogShellStar_pos hp

end LeanFormal.IUT