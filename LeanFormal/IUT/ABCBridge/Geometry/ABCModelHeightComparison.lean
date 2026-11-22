import LeanFormal.IUT.ABCBridge.Arithmetic.ABCInvariantHeight
import LeanFormal.IUT.ABCBridge.Arithmetic.ABCNonemptyOddBadSupport
import LeanFormal.IUT.ABCBridge.Geometry.FreyTateAnalyticInput
import LeanFormal.IUT.ABCBridge.Geometry.FreyWeierstrassCurve
import LeanFormal.IUT.ABCBridge.Geometry.LegendreWeierstrassCurve

/-!
# Canonical height comparisons for the actual ABC elliptic models

The Frey and Legendre models used here are the existing Mathlib Weierstrass
curves.  Their actual `j`-invariants are connected to the arithmetic invariant
by the exact formulas in their defining modules.  The conclusions compare
canonical Mathlib heights; they neither assert an isomorphism between the
models nor supply an IUT height estimate.

The transfer theorem records explicitly how any subsequently proved upper
estimate for either model's `j`-height controls the height of the ABC rational
point, and conversely how a bound for the latter controls `j`-height.

The final section records, for odd primes in the bad support of an actual ABC
triple, the placewise local data consumed by the Tate q-pilot chain: the
actual Frey `j` has negative valuation and norm greater than one, and its
inverse, the candidate input `q := j⁻¹` of `FreyTateAnalyticInput`, satisfies
the honest analytic hypotheses `q ≠ 0`, `q ≠ 1`, `‖q‖ < 1`.  No
uniformization, and no identification of `q` with a genuine Tate parameter,
is claimed.
-/

namespace LeanFormal.IUT

/-- An actual elliptic Weierstrass curve with the ABC j-invariant inherits
the canonical multiplicative comparison with `c⁶` and the logarithmic
comparison with six times the height of the actual point `a/c`. -/
theorem ellipticCurve_j_height_bounds_of_eq_abcJInvariant
    {a b c : ℕ} (h : IsABCTriple a b c)
    (curve : WeierstrassCurve ℚ) [curve.IsElliptic]
    (hj : curve.j = abcJInvariant a b c) :
    ((27 / 64 : ℝ) * (c : ℝ) ^ 6 ≤ Height.mulHeight₁ curve.j ∧
      Height.mulHeight₁ curve.j ≤ 256 * (c : ℝ) ^ 6) ∧
    (6 * Height.logHeight₁ (abcRationalPoint a c) + Real.log (27 / 64 : ℝ) ≤
        Height.logHeight₁ curve.j ∧
      Height.logHeight₁ curve.j ≤
        6 * Height.logHeight₁ (abcRationalPoint a c) + Real.log 256) := by
  rw [hj]
  exact ⟨abcJInvariant_mulHeight_bounds h,
    abcJInvariant_logHeight_bounds_abcRationalPoint h⟩

/-- Explicit upper-bound transfers in both directions.  The hypotheses
are actual numeric bounds on canonical heights, not conjectural IUT fields.
The multiplicative transfer uses the sixth power of the point height; the
logarithmic transfer uses the corresponding factor six. -/
theorem ellipticCurve_height_upper_bound_transfers_of_eq_abcJInvariant
    {a b c : ℕ} (h : IsABCTriple a b c)
    (curve : WeierstrassCurve ℚ) [curve.IsElliptic]
    (hj : curve.j = abcJInvariant a b c) (bound : ℝ) :
    (Height.mulHeight₁ curve.j ≤ bound →
      Height.mulHeight₁ (abcRationalPoint a c) ^ 6 ≤ (64 / 27 : ℝ) * bound) ∧
    (Height.mulHeight₁ (abcRationalPoint a c) ^ 6 ≤ bound →
      Height.mulHeight₁ curve.j ≤ 256 * bound) ∧
    (Height.logHeight₁ curve.j ≤ bound →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (bound - Real.log (27 / 64 : ℝ)) / 6) ∧
    (Height.logHeight₁ (abcRationalPoint a c) ≤ bound →
      Height.logHeight₁ curve.j ≤ 6 * bound + Real.log 256) := by
  have hmul := abcJInvariant_mulHeight_bounds_abcRationalPoint h
  have hlog := abcJInvariant_logHeight_bounds_abcRationalPoint h
  rw [← hj] at hmul hlog
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hj_bound
    nlinarith [hmul.1]
  · intro hpoint_bound
    nlinarith [hmul.2]
  · intro hj_bound
    nlinarith [hlog.1]
  · intro hpoint_bound
    nlinarith [hlog.2]

/-- The exact j-formula of the existing rational Frey model is the
arithmetic invariant whose canonical height was bounded above. -/
theorem rationalFreyWeierstrassCurve_j_eq_abcJInvariant
    {a b c : ℕ} (h : IsABCTriple a b c) :
    letI := rationalFreyWeierstrassCurve_isElliptic_of_isABCTriple h
    (rationalFreyWeierstrassCurve a b).j = abcJInvariant a b c := by
  letI := rationalFreyWeierstrassCurve_isElliptic_of_isABCTriple h
  simpa only [abcJInvariant, abcInvariantNumerator, abcInvariantPolynomial,
    abcInvariantDenominator, Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat]
    using rationalFreyWeierstrassCurve_j_of_isABCTriple h

/-- Canonical multiplicative and logarithmic j-height bounds for the
actual rational Frey curve, with its proved ellipticity instance. -/
theorem rationalFreyWeierstrassCurve_j_height_bounds
    {a b c : ℕ} (h : IsABCTriple a b c) :
    letI := rationalFreyWeierstrassCurve_isElliptic_of_isABCTriple h
    ((27 / 64 : ℝ) * (c : ℝ) ^ 6 ≤
        Height.mulHeight₁ (rationalFreyWeierstrassCurve a b).j ∧
      Height.mulHeight₁ (rationalFreyWeierstrassCurve a b).j ≤
        256 * (c : ℝ) ^ 6) ∧
    (6 * Height.logHeight₁ (abcRationalPoint a c) + Real.log (27 / 64 : ℝ) ≤
        Height.logHeight₁ (rationalFreyWeierstrassCurve a b).j ∧
      Height.logHeight₁ (rationalFreyWeierstrassCurve a b).j ≤
        6 * Height.logHeight₁ (abcRationalPoint a c) + Real.log 256) := by
  letI := rationalFreyWeierstrassCurve_isElliptic_of_isABCTriple h
  exact ellipticCurve_j_height_bounds_of_eq_abcJInvariant h
    (rationalFreyWeierstrassCurve a b)
    (rationalFreyWeierstrassCurve_j_eq_abcJInvariant h)

/-- A proved upper estimate for the actual Frey curve's j-height can be
transferred to the ABC point height with the displayed constants; the
converse transfer is also explicit.  No such upper estimate is assumed to
have been supplied by IUT. -/
theorem rationalFreyWeierstrassCurve_height_upper_bound_transfers
    {a b c : ℕ} (h : IsABCTriple a b c) (bound : ℝ) :
    letI := rationalFreyWeierstrassCurve_isElliptic_of_isABCTriple h
    (Height.mulHeight₁ (rationalFreyWeierstrassCurve a b).j ≤ bound →
      Height.mulHeight₁ (abcRationalPoint a c) ^ 6 ≤ (64 / 27 : ℝ) * bound) ∧
    (Height.mulHeight₁ (abcRationalPoint a c) ^ 6 ≤ bound →
      Height.mulHeight₁ (rationalFreyWeierstrassCurve a b).j ≤ 256 * bound) ∧
    (Height.logHeight₁ (rationalFreyWeierstrassCurve a b).j ≤ bound →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (bound - Real.log (27 / 64 : ℝ)) / 6) ∧
    (Height.logHeight₁ (abcRationalPoint a c) ≤ bound →
      Height.logHeight₁ (rationalFreyWeierstrassCurve a b).j ≤
        6 * bound + Real.log 256) := by
  letI := rationalFreyWeierstrassCurve_isElliptic_of_isABCTriple h
  exact ellipticCurve_height_upper_bound_transfers_of_eq_abcJInvariant h
    (rationalFreyWeierstrassCurve a b)
    (rationalFreyWeierstrassCurve_j_eq_abcJInvariant h) bound

/-- The exact j-formula of the existing Legendre model at the actual ABC
rational point is the same arithmetic invariant. -/
theorem abcRationalPoint_legendre_j_eq_abcJInvariant
    {a b c : ℕ} (h : IsABCTriple a b c) :
    letI := abcRationalPoint_legendre_isElliptic h
    (legendreWeierstrassCurve (abcRationalPoint a c)).j = abcJInvariant a b c := by
  letI := abcRationalPoint_legendre_isElliptic h
  simpa only [abcJInvariant, abcInvariantNumerator, abcInvariantPolynomial,
    abcInvariantDenominator, Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat]
    using abcRationalPoint_legendre_j_eq_abcExpression h

/-- Canonical multiplicative and logarithmic j-height bounds for the
actual Legendre curve at `a/c`, with its proved ellipticity instance. -/
theorem abcRationalPoint_legendre_j_height_bounds
    {a b c : ℕ} (h : IsABCTriple a b c) :
    letI := abcRationalPoint_legendre_isElliptic h
    ((27 / 64 : ℝ) * (c : ℝ) ^ 6 ≤
        Height.mulHeight₁ (legendreWeierstrassCurve (abcRationalPoint a c)).j ∧
      Height.mulHeight₁ (legendreWeierstrassCurve (abcRationalPoint a c)).j ≤
        256 * (c : ℝ) ^ 6) ∧
    (6 * Height.logHeight₁ (abcRationalPoint a c) + Real.log (27 / 64 : ℝ) ≤
        Height.logHeight₁ (legendreWeierstrassCurve (abcRationalPoint a c)).j ∧
      Height.logHeight₁ (legendreWeierstrassCurve (abcRationalPoint a c)).j ≤
        6 * Height.logHeight₁ (abcRationalPoint a c) + Real.log 256) := by
  letI := abcRationalPoint_legendre_isElliptic h
  exact ellipticCurve_j_height_bounds_of_eq_abcJInvariant h
    (legendreWeierstrassCurve (abcRationalPoint a c))
    (abcRationalPoint_legendre_j_eq_abcJInvariant h)

/-- Both directions of the upper-bound transfer for the actual Legendre
model.  These implications preserve the factors six and `256` and the
additive logarithmic constants exactly. -/
theorem abcRationalPoint_legendre_height_upper_bound_transfers
    {a b c : ℕ} (h : IsABCTriple a b c) (bound : ℝ) :
    letI := abcRationalPoint_legendre_isElliptic h
    (Height.mulHeight₁ (legendreWeierstrassCurve (abcRationalPoint a c)).j ≤ bound →
      Height.mulHeight₁ (abcRationalPoint a c) ^ 6 ≤ (64 / 27 : ℝ) * bound) ∧
    (Height.mulHeight₁ (abcRationalPoint a c) ^ 6 ≤ bound →
      Height.mulHeight₁ (legendreWeierstrassCurve (abcRationalPoint a c)).j ≤
        256 * bound) ∧
    (Height.logHeight₁ (legendreWeierstrassCurve (abcRationalPoint a c)).j ≤ bound →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (bound - Real.log (27 / 64 : ℝ)) / 6) ∧
    (Height.logHeight₁ (abcRationalPoint a c) ≤ bound →
      Height.logHeight₁ (legendreWeierstrassCurve (abcRationalPoint a c)).j ≤
        6 * bound + Real.log 256) := by
  letI := abcRationalPoint_legendre_isElliptic h
  exact ellipticCurve_height_upper_bound_transfers_of_eq_abcJInvariant h
    (legendreWeierstrassCurve (abcRationalPoint a c))
    (abcRationalPoint_legendre_j_eq_abcJInvariant h) bound

/-! ### Odd bad primes: the actual Frey `j` as local analytic input

For a prime `p` in the odd bad support `abcOddBadPrimeSupport a b c` of an
actual ABC triple (the odd part of the bad support: `p ≠ 2` and `p ∣ a b c`;
it is nonempty exactly for the nonexceptional triples), the actual
`j`-invariant of the rational Frey model has negative `p`-adic valuation and
norm greater than one.  Its inverse — the candidate input `q := j⁻¹` of
`FreyTateAnalyticInput`, viewed in `ℚ_[p]` — satisfies the honest analytic
hypotheses `q ≠ 0`, `q ≠ 1`, `‖q‖ < 1` consumed by the Tate q-series
interfaces.  The binding statement is the algebraic identity of
`freyAbcTateCandidateQ p a b c` with the actual curve's `j`-inverse; it is
**not** a uniformization statement and does **not** claim that `q` is the
genuine Tate parameter of the Frey curve. -/

/-- The actual rational Frey `j`-invariant has negative `p`-adic valuation at
any odd prime of the bad support.  Consumer: the local multiplicative-reduction
input of the Tate q-pilot chain at `p`. -/
theorem rationalFreyWeierstrassCurve_j_padicValRat_neg_of_mem_abcOddBadPrimeSupport
    {a b c p : ℕ} (h : IsABCTriple a b c)
    (hp : p ∈ abcOddBadPrimeSupport a b c) :
    letI : Fact p.Prime := ⟨(h.mem_abcOddBadPrimeSupport_iff.mp hp).1⟩
    letI := rationalFreyWeierstrassCurve_isElliptic_of_isABCTriple h
    padicValRat p (rationalFreyWeierstrassCurve a b).j < 0 := by
  letI : Fact p.Prime := ⟨(h.mem_abcOddBadPrimeSupport_iff.mp hp).1⟩
  letI := rationalFreyWeierstrassCurve_isElliptic_of_isABCTriple h
  exact rationalFreyWeierstrassCurve_j_padicValRat_neg_of_prime_ne_two_dvd_product h
    (h.mem_abcOddBadPrimeSupport_iff.mp hp).2.1
    (h.mem_abcOddBadPrimeSupport_iff.mp hp).2.2

/-- The actual rational Frey `j`-invariant has `p`-adic norm greater than one
at any odd prime of the bad support. -/
theorem rationalFreyWeierstrassCurve_j_padicNorm_gt_one_of_mem_abcOddBadPrimeSupport
    {a b c p : ℕ} (h : IsABCTriple a b c)
    (hp : p ∈ abcOddBadPrimeSupport a b c) :
    letI : Fact p.Prime := ⟨(h.mem_abcOddBadPrimeSupport_iff.mp hp).1⟩
    letI := rationalFreyWeierstrassCurve_isElliptic_of_isABCTriple h
    1 < padicNorm p (rationalFreyWeierstrassCurve a b).j := by
  letI : Fact p.Prime := ⟨(h.mem_abcOddBadPrimeSupport_iff.mp hp).1⟩
  letI := rationalFreyWeierstrassCurve_isElliptic_of_isABCTriple h
  exact rationalFreyWeierstrassCurve_j_padicNorm_gt_one_of_prime_ne_two_dvd_product h
    (h.mem_abcOddBadPrimeSupport_iff.mp hp).2.1
    (h.mem_abcOddBadPrimeSupport_iff.mp hp).2.2

/-- The actual rational Frey `j`-invariant, viewed in `ℚ_[p]`, has norm greater
than one at any odd prime of the bad support. -/
theorem rationalFreyWeierstrassCurve_j_cast_norm_gt_one_of_mem_abcOddBadPrimeSupport
    {a b c p : ℕ} (h : IsABCTriple a b c)
    (hp : p ∈ abcOddBadPrimeSupport a b c) :
    letI : Fact p.Prime := ⟨(h.mem_abcOddBadPrimeSupport_iff.mp hp).1⟩
    letI := rationalFreyWeierstrassCurve_isElliptic_of_isABCTriple h
    1 < ‖(((rationalFreyWeierstrassCurve a b).j : ℚ) : ℚ_[p])‖ := by
  letI : Fact p.Prime := ⟨(h.mem_abcOddBadPrimeSupport_iff.mp hp).1⟩
  letI := rationalFreyWeierstrassCurve_isElliptic_of_isABCTriple h
  exact rationalFreyWeierstrassCurve_j_cast_norm_gt_one_of_prime_ne_two_dvd_product h
    (h.mem_abcOddBadPrimeSupport_iff.mp hp).2.1
    (h.mem_abcOddBadPrimeSupport_iff.mp hp).2.2

/-- The inverse of the actual rational Frey `j`-invariant, viewed in `ℚ_[p]`,
is strictly contracted at any odd prime of the bad support: the `‖j⁻¹‖ < 1`
analytic-input condition of the Tate q-series interfaces. -/
theorem rationalFreyWeierstrassCurve_j_cast_inv_norm_lt_one_of_mem_abcOddBadPrimeSupport
    {a b c p : ℕ} (h : IsABCTriple a b c)
    (hp : p ∈ abcOddBadPrimeSupport a b c) :
    letI : Fact p.Prime := ⟨(h.mem_abcOddBadPrimeSupport_iff.mp hp).1⟩
    letI := rationalFreyWeierstrassCurve_isElliptic_of_isABCTriple h
    ‖(((rationalFreyWeierstrassCurve a b).j : ℚ) : ℚ_[p])⁻¹‖ < 1 := by
  letI : Fact p.Prime := ⟨(h.mem_abcOddBadPrimeSupport_iff.mp hp).1⟩
  letI := rationalFreyWeierstrassCurve_isElliptic_of_isABCTriple h
  exact rationalFreyWeierstrassCurve_j_cast_inv_norm_lt_one_of_prime_ne_two_dvd_product h
    (h.mem_abcOddBadPrimeSupport_iff.mp hp).2.1
    (h.mem_abcOddBadPrimeSupport_iff.mp hp).2.2

/-- The candidate input `freyAbcTateCandidateQ p a b c` of `FreyTateAnalyticInput`
equals the actual inverse `j`-invariant of the rational Frey model, viewed in
`ℚ_[p]`.  This binds the candidate object to the actual curve; it is not a
uniformization statement and does not identify the candidate with a genuine
Tate parameter. -/
theorem freyAbcTateCandidateQ_eq_rationalFreyWeierstrassCurve_j_cast_inv
    {a b c p : ℕ} [Fact p.Prime] (h : IsABCTriple a b c) :
    letI := rationalFreyWeierstrassCurve_isElliptic_of_isABCTriple h
    freyAbcTateCandidateQ p a b c =
      (((rationalFreyWeierstrassCurve a b).j : ℚ) : ℚ_[p])⁻¹ := by
  letI := rationalFreyWeierstrassCurve_isElliptic_of_isABCTriple h
  rw [rationalFreyWeierstrassCurve_j_eq_abcJInvariant_of_isABCTriple h]
  rfl

/-- The candidate input `q := j⁻¹` is nonzero at any odd prime of the bad
support: the first analytic hypothesis of the Tate interfaces. -/
theorem freyAbcTateCandidateQ_ne_zero_of_mem_abcOddBadPrimeSupport
    {a b c p : ℕ} (h : IsABCTriple a b c)
    (hp : p ∈ abcOddBadPrimeSupport a b c) :
    letI : Fact p.Prime := ⟨(h.mem_abcOddBadPrimeSupport_iff.mp hp).1⟩
    freyAbcTateCandidateQ p a b c ≠ 0 := by
  letI : Fact p.Prime := ⟨(h.mem_abcOddBadPrimeSupport_iff.mp hp).1⟩
  exact freyAbcTateCandidateQ_ne_zero h
    (h.mem_abcOddBadPrimeSupport_iff.mp hp).2.1
    (h.mem_abcOddBadPrimeSupport_iff.mp hp).2.2

/-- The candidate input `q := j⁻¹` satisfies the contraction hypothesis
`‖q‖ < 1` of the Tate q-series interfaces at any odd prime of the bad
support. -/
theorem freyAbcTateCandidateQ_norm_lt_one_of_mem_abcOddBadPrimeSupport
    {a b c p : ℕ} (h : IsABCTriple a b c)
    (hp : p ∈ abcOddBadPrimeSupport a b c) :
    letI : Fact p.Prime := ⟨(h.mem_abcOddBadPrimeSupport_iff.mp hp).1⟩
    ‖freyAbcTateCandidateQ p a b c‖ < 1 := by
  letI : Fact p.Prime := ⟨(h.mem_abcOddBadPrimeSupport_iff.mp hp).1⟩
  exact freyAbcTateCandidateQ_norm_lt_one h
    (h.mem_abcOddBadPrimeSupport_iff.mp hp).2.1
    (h.mem_abcOddBadPrimeSupport_iff.mp hp).2.2

/-- The candidate input `q := j⁻¹` is not one at any odd prime of the bad
support: the hypothesis of the unit-side Tate interfaces on `q`. -/
theorem freyAbcTateCandidateQ_ne_one_of_mem_abcOddBadPrimeSupport
    {a b c p : ℕ} (h : IsABCTriple a b c)
    (hp : p ∈ abcOddBadPrimeSupport a b c) :
    letI : Fact p.Prime := ⟨(h.mem_abcOddBadPrimeSupport_iff.mp hp).1⟩
    freyAbcTateCandidateQ p a b c ≠ 1 := by
  letI : Fact p.Prime := ⟨(h.mem_abcOddBadPrimeSupport_iff.mp hp).1⟩
  exact freyAbcTateCandidateQ_ne_one h
    (h.mem_abcOddBadPrimeSupport_iff.mp hp).2.1
    (h.mem_abcOddBadPrimeSupport_iff.mp hp).2.2

/-- Every nonexceptional actual ABC triple has an odd bad prime at which the
actual Frey `j` has negative valuation and greater-than-one norm, and the
candidate input `q := j⁻¹` satisfies all three analytic hypotheses of the Tate
q-series interfaces.  This is the packaged local input of the Tate q-pilot
chain; it is not a uniformization statement. -/
theorem exists_odd_bad_prime_freyAbcTateAnalyticInput
    {a b c : ℕ} (h : IsABCTriple a b c) (hne : (a, b, c) ≠ (1, 1, 2)) :
    ∃ p : ℕ, ∃ hp : p.Prime, p ≠ 2 ∧ p ∈ abcOddBadPrimeSupport a b c ∧
      (letI : Fact p.Prime := ⟨hp⟩
       letI := rationalFreyWeierstrassCurve_isElliptic_of_isABCTriple h
       padicValRat p (rationalFreyWeierstrassCurve a b).j < 0 ∧
       1 < ‖(((rationalFreyWeierstrassCurve a b).j : ℚ) : ℚ_[p])‖ ∧
       ‖freyAbcTateCandidateQ p a b c‖ < 1 ∧
       freyAbcTateCandidateQ p a b c ≠ 0 ∧
       freyAbcTateCandidateQ p a b c ≠ 1) := by
  obtain ⟨p, hp, hpne, hdiv⟩ := h.exists_odd_prime_dvd_product hne
  haveI : Fact p.Prime := ⟨hp⟩
  refine ⟨p, hp, hpne, h.mem_abcOddBadPrimeSupport_iff.mpr ⟨hp, hpne, hdiv⟩, ?_⟩
  letI := rationalFreyWeierstrassCurve_isElliptic_of_isABCTriple h
  exact ⟨rationalFreyWeierstrassCurve_j_padicValRat_neg_of_prime_ne_two_dvd_product h hpne hdiv,
    rationalFreyWeierstrassCurve_j_cast_norm_gt_one_of_prime_ne_two_dvd_product h hpne hdiv,
    freyAbcTateCandidateQ_norm_lt_one h hpne hdiv,
    freyAbcTateCandidateQ_ne_zero h hpne hdiv,
    freyAbcTateCandidateQ_ne_one h hpne hdiv⟩

end LeanFormal.IUT
