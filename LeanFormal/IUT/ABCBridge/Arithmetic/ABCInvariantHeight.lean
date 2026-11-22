import Mathlib.NumberTheory.Height.NumberField
import Mathlib.Tactic
import LeanFormal.IUT.ABCBridge.Statement
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPointDictionary
import LeanFormal.IUT.ABCBridge.Arithmetic.ABCInvariantCoprimality

/-!
# Canonical rational height of the ABC elliptic invariant

The relevant invariant is the rational number
`256 * (a² + ab + b²)³ / (a² b² c²)`, where `a + b = c`.
The comparison is with Mathlib's canonical rational height.  The real estimates
below are the archimedean part of the comparison.  Reduction of the rational
fraction must be controlled separately before the lower height bound follows.
-/

namespace LeanFormal.IUT

/-- The reduced numerator of a nonnegative rational fraction is obtained
by dividing the natural numerator by the natural gcd. -/
theorem abcInvariantFraction_num_natAbs (numerator denominator : ℕ)
    (hdenominator : 0 < denominator) :
    ((numerator : ℚ) / denominator).num.natAbs =
      numerator / Nat.gcd numerator denominator := by
  have hrepresentation : (numerator : ℚ) / denominator =
      Rat.divInt (numerator : ℤ) (denominator : ℤ) := by
    simp only [Rat.divInt_eq_div, Int.cast_natCast]
  have hdenominator_int : 0 < (denominator : ℤ) := by exact_mod_cast hdenominator
  rw [hrepresentation, Rat.num_divInt, Int.sign_eq_one_of_pos hdenominator_int,
    one_mul, Int.gcd_natCast_natCast, ← Int.natCast_ediv,
    Int.natAbs_natCast, Nat.gcd_comm]

/-- The reduced denominator of a nonnegative rational fraction is obtained
by dividing the natural denominator by the same gcd. -/
theorem abcInvariantFraction_den (numerator denominator : ℕ)
    (hdenominator : 0 < denominator) :
    ((numerator : ℚ) / denominator).den =
      denominator / Nat.gcd numerator denominator := by
  have hrepresentation : (numerator : ℚ) / denominator =
      Rat.divInt (numerator : ℤ) (denominator : ℤ) := by
    simp only [Rat.divInt_eq_div, Int.cast_natCast]
  have hdenominator_int : (denominator : ℤ) ≠ 0 := by
    exact_mod_cast hdenominator.ne'
  rw [hrepresentation, Rat.den_divInt, if_neg hdenominator_int,
    Int.natAbs_natCast, Int.gcd_natCast_natCast, Nat.gcd_comm]

/-- This formula uses Mathlib's canonical rational height and the actual
reduced numerator and denominator; no separate height is introduced. -/
theorem abcInvariantFraction_mulHeight_eq (numerator denominator : ℕ)
    (hdenominator : 0 < denominator) :
    Height.mulHeight₁ ((numerator : ℚ) / denominator) =
      max ((numerator / Nat.gcd numerator denominator : ℕ) : ℝ)
        ((denominator / Nat.gcd numerator denominator : ℕ) : ℝ) := by
  rw [Rat.mulHeight₁_eq_max,
    abcInvariantFraction_num_natAbs numerator denominator hdenominator,
    abcInvariantFraction_den numerator denominator hdenominator, Nat.cast_max]

/-- Reduction of a fraction cannot increase either of its natural
coordinates, and therefore cannot increase their maximum. -/
theorem abcInvariantFraction_mulHeight_le_max (numerator denominator : ℕ)
    (hdenominator : 0 < denominator) :
    Height.mulHeight₁ ((numerator : ℚ) / denominator) ≤
      max (numerator : ℝ) (denominator : ℝ) := by
  rw [abcInvariantFraction_mulHeight_eq numerator denominator hdenominator]
  exact max_le_max
    (by exact_mod_cast Nat.div_le_self numerator (Nat.gcd numerator denominator))
    (by exact_mod_cast Nat.div_le_self denominator (Nat.gcd numerator denominator))

/-- A proved upper bound on the actual cancellation gcd gives a lower
bound on the canonical height from the unreduced numerator. -/
theorem abcInvariantFraction_div_cancellation_le_mulHeight
    (numerator denominator cancellationBound : ℕ)
    (hdenominator : 0 < denominator)
    (hcancellation : Nat.gcd numerator denominator ≤ cancellationBound) :
    (numerator : ℝ) / cancellationBound ≤
      Height.mulHeight₁ ((numerator : ℚ) / denominator) := by
  have hgcd : 0 < Nat.gcd numerator denominator := by
    simpa [Nat.gcd_comm] using Nat.gcd_pos_of_pos_left numerator hdenominator
  have hgcd_real : 0 < (Nat.gcd numerator denominator : ℝ) := by exact_mod_cast hgcd
  have hbound_real : (Nat.gcd numerator denominator : ℝ) ≤ cancellationBound := by
    exact_mod_cast hcancellation
  calc
    (numerator : ℝ) / cancellationBound ≤
        (numerator : ℝ) / Nat.gcd numerator denominator :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg numerator) hgcd_real hbound_real
    _ = ((numerator / Nat.gcd numerator denominator : ℕ) : ℝ) :=
      (Nat.cast_div (Nat.gcd_dvd_left numerator denominator) hgcd_real.ne').symm
    _ ≤ Height.mulHeight₁ ((numerator : ℚ) / denominator) := by
      rw [abcInvariantFraction_mulHeight_eq numerator denominator hdenominator]
      exact le_max_left _ _

/-- The polynomial in the numerator of the ABC elliptic invariant lies below
the square of the sum of its nonnegative arguments. -/
theorem abcInvariantPolynomial_le_sum_sq {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hsum : a + b = c) :
    a ^ 2 + a * b + b ^ 2 ≤ c ^ 2 := by
  rw [← hsum]
  nlinarith [mul_nonneg ha hb]

/-- The polynomial in the numerator of the ABC elliptic invariant is at
least three quarters of the square of the sum. -/
theorem abcInvariantPolynomial_ge_three_quarters_sum_sq {a b c : ℝ}
    (hsum : a + b = c) :
    (3 / 4 : ℝ) * c ^ 2 ≤ a ^ 2 + a * b + b ^ 2 := by
  rw [← hsum]
  nlinarith [sq_nonneg (a - b)]

/-- Cubing the numerator polynomial gives the explicit degree-six upper
bound used by the rational-height comparison. -/
theorem abcInvariantPolynomial_cube_le_sum_pow_six {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hsum : a + b = c) :
    (a ^ 2 + a * b + b ^ 2) ^ 3 ≤ c ^ 6 := by
  calc
    (a ^ 2 + a * b + b ^ 2) ^ 3 ≤ (c ^ 2) ^ 3 := by
      gcongr
      exact abcInvariantPolynomial_le_sum_sq ha hb hsum
    _ = c ^ 6 := by ring

/-- The constant `27/64` is the cube of the sharp quadratic constant
`3/4`; it does not arise from a change in the height normalization. -/
theorem abcInvariantPolynomial_cube_ge_sum_pow_six {a b c : ℝ}
    (hsum : a + b = c) :
    (27 / 64 : ℝ) * c ^ 6 ≤ (a ^ 2 + a * b + b ^ 2) ^ 3 := by
  calc
    (27 / 64 : ℝ) * c ^ 6 = ((3 / 4 : ℝ) * c ^ 2) ^ 3 := by ring
    _ ≤ (a ^ 2 + a * b + b ^ 2) ^ 3 := by
      gcongr
      exact abcInvariantPolynomial_ge_three_quarters_sum_sq hsum

/-- The unreduced denominator of the ABC elliptic invariant has the same
degree-six upper bound. -/
theorem abcInvariantDenominator_le_sum_pow_six {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hsum : a + b = c) :
    a ^ 2 * b ^ 2 * c ^ 2 ≤ c ^ 6 := by
  have hac : a ≤ c := by linarith
  have hbc : b ≤ c := by linarith
  have hc : 0 ≤ c := by linarith
  calc
    a ^ 2 * b ^ 2 * c ^ 2 ≤ c ^ 2 * c ^ 2 * c ^ 2 := by gcongr
    _ = c ^ 6 := by ring

/-- An actual ABC triple has an invariant whose canonical rational
multiplicative height is at most `256 c⁶`. -/
theorem abcJInvariant_mulHeight_le {a b c : ℕ} (h : IsABCTriple a b c) :
    Height.mulHeight₁ (abcJInvariant a b c) ≤ 256 * (c : ℝ) ^ 6 := by
  obtain ⟨ha, hb, hsum, _hcoprime⟩ :=
    (isABCTriple_iff_positivePrimitiveAdditiveTriple a b c).mp h
  have hc : 0 < c := by omega
  have hsum_real : (a : ℝ) + (b : ℝ) = (c : ℝ) := by exact_mod_cast hsum
  have hdenominator : 0 < abcInvariantDenominator a b c := by
    dsimp [abcInvariantDenominator]
    positivity
  have hpolynomial := abcInvariantPolynomial_cube_le_sum_pow_six
    (Nat.cast_nonneg a : (0 : ℝ) ≤ a) (Nat.cast_nonneg b) hsum_real
  have hnumerator : (abcInvariantNumerator a b : ℝ) ≤ 256 * (c : ℝ) ^ 6 := by
    dsimp [abcInvariantNumerator, abcInvariantPolynomial]
    push_cast
    nlinarith
  have hdenominator_le : (abcInvariantDenominator a b c : ℝ) ≤ (c : ℝ) ^ 6 := by
    simpa only [abcInvariantDenominator, Nat.cast_mul, Nat.cast_pow] using
      abcInvariantDenominator_le_sum_pow_six
        (Nat.cast_nonneg a : (0 : ℝ) ≤ a) (Nat.cast_nonneg b) hsum_real
  change Height.mulHeight₁
    ((abcInvariantNumerator a b : ℚ) / abcInvariantDenominator a b c) ≤ _
  refine (abcInvariantFraction_mulHeight_le_max _ _ hdenominator).trans ?_
  exact max_le hnumerator (hdenominator_le.trans (by nlinarith [sq_nonneg ((c : ℝ) ^ 3)]))

/-- The lower height bound uses the actual gcd cancellation estimate
proved for primitive ABC triples. -/
theorem abcJInvariant_mulHeight_ge {a b c : ℕ} (h : IsABCTriple a b c) :
    (27 / 64 : ℝ) * (c : ℝ) ^ 6 ≤ Height.mulHeight₁ (abcJInvariant a b c) := by
  obtain ⟨ha, hb, hsum, _hcoprime⟩ :=
    (isABCTriple_iff_positivePrimitiveAdditiveTriple a b c).mp h
  have hc : 0 < c := by omega
  have hsum_real : (a : ℝ) + (b : ℝ) = (c : ℝ) := by exact_mod_cast hsum
  have hdenominator : 0 < abcInvariantDenominator a b c := by
    dsimp [abcInvariantDenominator]
    positivity
  have hcancellation : Nat.gcd (abcInvariantNumerator a b)
      (abcInvariantDenominator a b c) ≤ 256 := h.abcInvariantCancellation_le_256
  have hheight := abcInvariantFraction_div_cancellation_le_mulHeight
    (abcInvariantNumerator a b) (abcInvariantDenominator a b c) 256
    hdenominator hcancellation
  have hnumerator : (abcInvariantNumerator a b : ℝ) / 256 =
      ((a : ℝ) ^ 2 + (a : ℝ) * (b : ℝ) + (b : ℝ) ^ 2) ^ 3 := by
    simp only [abcInvariantNumerator, abcInvariantPolynomial, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_pow, Nat.cast_add]
    ring
  change (27 / 64 : ℝ) * (c : ℝ) ^ 6 ≤ Height.mulHeight₁
    ((abcInvariantNumerator a b : ℚ) / abcInvariantDenominator a b c)
  rw [Nat.cast_ofNat, hnumerator] at hheight
  exact (abcInvariantPolynomial_cube_ge_sum_pow_six hsum_real).trans hheight

/-- Both explicit constants in the canonical multiplicative height
comparison are recorded together. -/
theorem abcJInvariant_mulHeight_bounds {a b c : ℕ} (h : IsABCTriple a b c) :
    (27 / 64 : ℝ) * (c : ℝ) ^ 6 ≤ Height.mulHeight₁ (abcJInvariant a b c) ∧
      Height.mulHeight₁ (abcJInvariant a b c) ≤ 256 * (c : ℝ) ^ 6 :=
  ⟨abcJInvariant_mulHeight_ge h, abcJInvariant_mulHeight_le h⟩

/-- Taking logarithms of the upper multiplicative bound yields the
explicit additive error `log 256`. -/
theorem abcJInvariant_logHeight_le {a b c : ℕ} (h : IsABCTriple a b c) :
    Height.logHeight₁ (abcJInvariant a b c) ≤ 6 * Real.log (c : ℝ) + Real.log 256 := by
  obtain ⟨ha, hb, hsum, _hcoprime⟩ :=
    (isABCTriple_iff_positivePrimitiveAdditiveTriple a b c).mp h
  have hc : 0 < c := by omega
  have hc_real : 0 < (c : ℝ) := by exact_mod_cast hc
  have hlog := Real.log_le_log (Height.mulHeight₁_pos (abcJInvariant a b c))
    (abcJInvariant_mulHeight_le h)
  rw [Height.logHeight₁_eq_log_mulHeight₁]
  calc
    Real.log (Height.mulHeight₁ (abcJInvariant a b c)) ≤
        Real.log (256 * (c : ℝ) ^ 6) := hlog
    _ = 6 * Real.log (c : ℝ) + Real.log 256 := by
      rw [Real.log_mul (by norm_num) (pow_ne_zero _ hc_real.ne'), Real.log_pow]
      norm_num
      ring

/-- Taking logarithms of the lower multiplicative bound yields the
explicit additive error `log (27/64)`. -/
theorem abcJInvariant_logHeight_ge {a b c : ℕ} (h : IsABCTriple a b c) :
    6 * Real.log (c : ℝ) + Real.log (27 / 64 : ℝ) ≤
      Height.logHeight₁ (abcJInvariant a b c) := by
  obtain ⟨ha, hb, hsum, _hcoprime⟩ :=
    (isABCTriple_iff_positivePrimitiveAdditiveTriple a b c).mp h
  have hc : 0 < c := by omega
  have hc_real : 0 < (c : ℝ) := by exact_mod_cast hc
  have hlower_pos : (0 : ℝ) < (27 / 64 : ℝ) * (c : ℝ) ^ 6 := by positivity
  have hlog := Real.log_le_log hlower_pos (abcJInvariant_mulHeight_ge h)
  rw [Height.logHeight₁_eq_log_mulHeight₁]
  calc
    6 * Real.log (c : ℝ) + Real.log (27 / 64 : ℝ) =
        Real.log ((27 / 64 : ℝ) * (c : ℝ) ^ 6) := by
      rw [Real.log_mul (by norm_num) (pow_ne_zero _ hc_real.ne'), Real.log_pow]
      norm_num
      ring
    _ ≤ Real.log (Height.mulHeight₁ (abcJInvariant a b c)) := hlog

/-- The exact logarithmic comparison consumed by the bridge from the
elliptic invariant to the largest coordinate of an ABC triple. -/
theorem abcJInvariant_logHeight_bounds {a b c : ℕ} (h : IsABCTriple a b c) :
    6 * Real.log (c : ℝ) + Real.log (27 / 64 : ℝ) ≤
        Height.logHeight₁ (abcJInvariant a b c) ∧
      Height.logHeight₁ (abcJInvariant a b c) ≤
        6 * Real.log (c : ℝ) + Real.log 256 :=
  ⟨abcJInvariant_logHeight_ge h, abcJInvariant_logHeight_le h⟩

/-- Rewriting by the actual ABC rational-point height dictionary gives
the multiplicative comparison in terms of the height of `a/c`. -/
theorem abcJInvariant_mulHeight_bounds_abcRationalPoint {a b c : ℕ}
    (h : IsABCTriple a b c) :
    (27 / 64 : ℝ) * Height.mulHeight₁ (abcRationalPoint a c) ^ 6 ≤
        Height.mulHeight₁ (abcJInvariant a b c) ∧
      Height.mulHeight₁ (abcJInvariant a b c) ≤
        256 * Height.mulHeight₁ (abcRationalPoint a c) ^ 6 := by
  rw [abcRationalPoint_mulHeight₁ h]
  exact abcJInvariant_mulHeight_bounds h

/-- The invariant height differs from six times the ABC rational-point
height by a quantity between the two explicit logarithmic constants. -/
theorem abcJInvariant_logHeight_bounds_abcRationalPoint {a b c : ℕ}
    (h : IsABCTriple a b c) :
    6 * Height.logHeight₁ (abcRationalPoint a c) + Real.log (27 / 64 : ℝ) ≤
        Height.logHeight₁ (abcJInvariant a b c) ∧
      Height.logHeight₁ (abcJInvariant a b c) ≤
        6 * Height.logHeight₁ (abcRationalPoint a c) + Real.log 256 := by
  rw [abcRationalPoint_logHeight₁ h]
  exact abcJInvariant_logHeight_bounds h

end LeanFormal.IUT
