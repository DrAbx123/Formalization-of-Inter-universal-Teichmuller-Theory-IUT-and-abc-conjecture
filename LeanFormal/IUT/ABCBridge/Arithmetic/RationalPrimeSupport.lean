/-
  Arithmetic prime support and arithmetic weight of a rational number, and their
  evaluation at the actual ABC rational point `abcRationalPoint a c`.

  This is arithmetic bridge material for the IUT IV Cor. 2.3 specialization: the
  finite support of the three coordinates of `x = a / c` is the set of primes
  dividing `a * b * c`, and the corresponding log-weight is `log(radical(a*b*c))`.

  The support defined here is an *arithmetic* prime support.  It is intentionally
  not named or claimed to be the geometric conductor, whose identification and the
  IUT estimate are not part of this module.
-/
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPointDictionary
import LeanFormal.IUT.Foundations.Arithmetic.Radical
import Mathlib.Tactic

namespace LeanFormal.IUT

/-- Arithmetic prime support of a rational number `x`:

the union of the prime factors of the three intrinsic integer coordinates
`u = x.num.natAbs`, `v = ((x.den : ℤ) - x.num).natAbs`, `w = x.den`.

For a reduced fraction `x = u / w` these coordinates are the numerator, the
`denominator - numerator` gap, and the denominator; the Finset union removes
repeated primes, so the support is a set, not a multiset. -/
def arithmeticPrimeSupport (x : ℚ) : Finset ℕ :=
  x.num.natAbs.primeFactors ∪ (((x.den : ℤ) - x.num).natAbs).primeFactors ∪
    x.den.primeFactors

/-- Arithmetic weight of a rational number `x`: the sum of `log p` over the
arithmetic prime support of `x`.  This is the arithmetic weight used by the
ABC rational-point specialization. -/
noncomputable def arithmeticWeight (x : ℚ) : ℝ :=
  ∑ p ∈ arithmeticPrimeSupport x, Real.log (p : ℝ)

/-- The project radical is positive after casting to `ℝ`. -/
theorem natRadical_cast_pos (n : ℕ) : (0 : ℝ) < (natRadical n : ℝ) := by
  exact_mod_cast natRadical_pos n

/-- Logarithm of the project radical as the finite sum of `log p` over the prime
factors.  Valid for every `n`; for `n = 0` both sides are `0` because
`natRadical 0 = 1` and `0.primeFactors = ∅`. -/
theorem natRadical_cast_log_eq_sum_primeFactors (n : ℕ) :
    Real.log ((natRadical n : ℕ) : ℝ) = ∑ p ∈ n.primeFactors, Real.log (p : ℝ) := by
  rw [natRadical_eq_prod_primeFactors]
  rw [Nat.cast_prod]
  exact Real.log_prod fun p hp => by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero

/-- At the actual ABC rational point `x = abcRationalPoint a c`, the arithmetic
prime support is exactly the prime-factor set of `a * b * c`. -/
theorem arithmeticPrimeSupport_abcRationalPoint {a b c : ℕ} (h : IsABCTriple a b c) :
    arithmeticPrimeSupport (abcRationalPoint a c) = (a * b * c).primeFactors := by
  have hnum : (abcRationalPoint a c).num.natAbs = a := abcRationalPoint_num_natAbs h
  have hden : (abcRationalPoint a c).den = c := abcRationalPoint_den h
  have hgap :
      (((abcRationalPoint a c).den : ℤ) - (abcRationalPoint a c).num).natAbs = b := by
    rw [abcRationalPoint_den_sub_num h, Int.natAbs_natCast]
  obtain ⟨ha, hb, hsum, hcop⟩ := h
  have ha0 : a ≠ 0 := by omega
  have hb0 : b ≠ 0 := by omega
  have hc0 : c ≠ 0 := by omega
  unfold arithmeticPrimeSupport
  rw [hnum, hgap, hden]
  rw [Nat.primeFactors_mul (Nat.mul_ne_zero ha0 hb0) hc0]
  rw [Nat.primeFactors_mul ha0 hb0]

/-- At the actual ABC rational point `x = abcRationalPoint a c`, the arithmetic
weight is `log(radical(a * b * c))` for the project radical `natRadical`. -/
theorem arithmeticWeight_abcRationalPoint {a b c : ℕ} (h : IsABCTriple a b c) :
    arithmeticWeight (abcRationalPoint a c) = Real.log (natRadical (a * b * c) : ℝ) := by
  unfold arithmeticWeight
  rw [arithmeticPrimeSupport_abcRationalPoint h]
  exact (natRadical_cast_log_eq_sum_primeFactors (a * b * c)).symm

end LeanFormal.IUT
