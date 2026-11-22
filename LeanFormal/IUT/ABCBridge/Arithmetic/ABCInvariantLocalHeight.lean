/-
  Local height of the actual ABC rational point and Frey/Legendre invariant.

  This specializes the canonical-height decomposition of
  `LeanFormal.IUT.ABCBridge.Arithmetic.RationalLocalHeightDecomposition` to the two objects of this
  line that are already consumed by the ABC bridge:

  * the actual rational point `x = abcRationalPoint a c = a / c` of an `IsABCTriple a b c`
    (`RationalPointDictionary`), and
  * the actual Frey/Legendre invariant `j = abcJInvariant a b c = 256 (a² + ab + b²)³ / (a²b²c²)`
    with its reduced coordinates as studied in `ABCInvariantCoprimality`,
    `ABCInvariantLocalValuations` and `ABCInvariantHeight`.

  Main results (all about the actual Mathlib height `Height.logHeight₁` and the actual local
  valuations `padicValRat` of these two objects; no replaced rational-expression model is used):

  * `abcRationalPoint_logHeight₁_eq_sum_den_factorization`, `..._eq_sum_padicValNat`,
    `..._eq_sum_max_zero_neg_padicValRat`: the canonical height of the point is the finite sum
    `Σ_{p ∣ c} v_p(c) log p` of denominator valuations; the archimedean term `max 0 (log |x|)`
    vanishes because `a < c` (`abcRationalPoint_log_abs_le_zero`);
  * `abcRationalPoint_logHeight₁_eq_sum_arithmeticPrimeSupport`: the same height, indexed by the
    accepted `arithmeticPrimeSupport x` of `RationalPrimeSupport` with weights `max 0 (−v_p(x))`.
    This puts the canonical height on exactly the support whose weights are summed in
    `arithmeticWeight x`; no comparison or estimate of those two sums is proved here;
  * `abcJInvariant_logHeight₁_eq_max_factorization`: the exact height of the reduced invariant as
    the maximum of the two prime-factorization sums of its reduced numerator and denominator;
  * `abcJInvariant_logHeight₁_eq_archimedean_add_den_factorization`,
    `abcJInvariant_logHeight₁_eq_archimedean_add_den_padicValRat` and
    `abcJInvariant_logHeight₁_eq_sum_all_places`: the same height as the archimedean term
    `max 0 (log j)` plus the finite-valuation terms `max 0 (−v_p(j)) log p` of its denominator;
  * explicit valuation coefficients: `abcJInvariant_den_factorization_of_prime_ne_two_dvd_product`
    (`2 (v_p(a) + v_p(b) + v_p(c))` at odd `p ∣ abc`), `abcJInvariant_den_factorization_eq` (the
    `2`-adic boundary `2 v₂(abc) − 8`) and `abcJInvariant_num_factorization_eq`
    (`8 [p = 2] + 3 v_p(a² + ab + b²) − v_p(cancel)`), with `cancel = abcInvariantCancellation`.

  Not established here: any ABC inequality, any comparison of the weighted height sum with
  `arithmeticWeight`, any conductor identification, and no analytic estimate is used.
-/
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalLocalHeightDecomposition
import LeanFormal.IUT.ABCBridge.Arithmetic.ABCInvariantHeight
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPrimeSupport
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalBoundaryPrimeSupport

namespace LeanFormal.IUT

/-! ### The actual ABC rational point `x = a / c` -/

/-- The archimedean absolute value of the actual ABC point is `< 1`: `a < c` for an additive
positive triple. -/
theorem abcRationalPoint_log_abs_le_zero {a b c : ℕ} (h : IsABCTriple a b c) :
    Real.log |(abcRationalPoint a c : ℝ)| ≤ 0 := by
  have ha : 0 < a := h.1
  have hb : 0 < b := h.2.1
  have hsum : a + b = c := h.2.2.1
  have hc : 0 < c := by omega
  have hac : a < c := by omega
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  have habs : |(abcRationalPoint a c : ℝ)| = (a : ℝ) / (c : ℝ) := by
    rw [abcRationalPoint_eq_div]
    push_cast
    exact abs_of_nonneg (div_nonneg haR.le hcR.le)
  have hlt : (a : ℝ) / (c : ℝ) < 1 := by
    rw [div_lt_one hcR]
    exact_mod_cast hac
  rw [habs]
  calc Real.log ((a : ℝ) / (c : ℝ)) ≤ Real.log 1 := Real.log_le_log (div_pos haR hcR) hlt.le
    _ = 0 := Real.log_one

/-- The canonical height of the actual ABC point is the prime-factorization sum over `c`. -/
theorem abcRationalPoint_logHeight₁_eq_sum_den_factorization {a b c : ℕ}
    (h : IsABCTriple a b c) :
    Height.logHeight₁ (abcRationalPoint a c) =
      ∑ p ∈ c.primeFactors, (c.factorization p : ℝ) * Real.log p := by
  rw [rational_logHeight₁_eq_sum_den_factorization_of_log_abs_nonpos _
    (abcRationalPoint_ne_zero h) (abcRationalPoint_log_abs_le_zero h), abcRationalPoint_den h]

/-- The same height with `padicValNat` weights. -/
theorem abcRationalPoint_logHeight₁_eq_sum_padicValNat {a b c : ℕ}
    (h : IsABCTriple a b c) :
    Height.logHeight₁ (abcRationalPoint a c) =
      ∑ p ∈ c.primeFactors, (padicValNat p c : ℝ) * Real.log p := by
  rw [abcRationalPoint_logHeight₁_eq_sum_den_factorization h]
  exact Finset.sum_congr rfl fun p hp => by
    rw [Nat.factorization_def c (Nat.prime_of_mem_primeFactors hp)]

/-- The denominator valuation of the point is `(−v_p(x)).toNat`: the height's finite terms are the
actual local valuations of the point. -/
theorem abcRationalPoint_den_factorization_eq_neg_padicValRat_toNat {a b c p : ℕ}
    (h : IsABCTriple a b c) (hp : p.Prime) :
    c.factorization p = (-(padicValRat p (abcRationalPoint a c))).toNat := by
  have h1 : (abcRationalPoint a c).den.factorization p =
      (-(padicValRat p (abcRationalPoint a c))).toNat :=
    rat_den_factorization_eq_neg_padicValRat_toNat p hp (abcRationalPoint a c)
  rw [abcRationalPoint_den h] at h1
  exact h1

/-- The canonical height of the point as a sum of local valuation truncations of `x`. -/
theorem abcRationalPoint_logHeight₁_eq_sum_neg_padicValRat_toNat {a b c : ℕ}
    (h : IsABCTriple a b c) :
    Height.logHeight₁ (abcRationalPoint a c) =
      ∑ p ∈ c.primeFactors,
        ((-(padicValRat p (abcRationalPoint a c))).toNat : ℝ) * Real.log p := by
  rw [abcRationalPoint_logHeight₁_eq_sum_den_factorization h]
  exact Finset.sum_congr rfl fun p hp => by
    rw [abcRationalPoint_den_factorization_eq_neg_padicValRat_toNat h
      (Nat.prime_of_mem_primeFactors hp)]

/-- The canonical height of the point with the standard nonarchimedean local terms
`max 0 (−v_p(x)) log p`. -/
theorem abcRationalPoint_logHeight₁_eq_sum_max_zero_neg_padicValRat {a b c : ℕ}
    (h : IsABCTriple a b c) :
    Height.logHeight₁ (abcRationalPoint a c) =
      ∑ p ∈ c.primeFactors,
        max 0 (-(padicValRat p (abcRationalPoint a c) : ℝ)) * Real.log p := by
  rw [abcRationalPoint_logHeight₁_eq_sum_neg_padicValRat_toNat h]
  exact Finset.sum_congr rfl fun p _ => by
    rw [int_toNat_neg_cast_eq_max_zero (padicValRat p (abcRationalPoint a c))]

/-- At a prime dividing `c`, the local term of the point is exactly the valuation of `c`. -/
theorem abcRationalPoint_max_zero_neg_padicValRat_eq_padicValNat_of_prime_dvd {a b c p : ℕ}
    (h : IsABCTriple a b c) (hp : p.Prime) (hpc : p ∣ c) :
    max 0 (-(padicValRat p (abcRationalPoint a c) : ℝ)) = (padicValNat p c : ℝ) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpa : ¬ p ∣ a := fun hpa =>
    not_coprime_of_prime_dvd_both hp h.coprime_left_right hpa hpc
  have hva : padicValNat p a = 0 := padicValNat.eq_zero_of_not_dvd hpa
  rw [padicValRat_abcRationalPoint p h, hva, Nat.cast_zero, zero_sub,
    Int.cast_neg, Int.cast_natCast, neg_neg,
    max_eq_right (Nat.cast_nonneg (padicValNat p c))]

/-- **Canonical height of the actual ABC point on the arithmetic support.**  The height is the
weighted sum, over exactly the accepted `arithmeticPrimeSupport` of the point, of the local terms
`max 0 (−v_p(x)) log p`.  The unweighted sum over this same support is `arithmeticWeight x`; the
comparison of the two sums is not part of this file. -/
theorem abcRationalPoint_logHeight₁_eq_sum_arithmeticPrimeSupport {a b c : ℕ}
    (h : IsABCTriple a b c) :
    Height.logHeight₁ (abcRationalPoint a c) =
      ∑ p ∈ arithmeticPrimeSupport (abcRationalPoint a c),
        max 0 (-(padicValRat p (abcRationalPoint a c) : ℝ)) * Real.log p := by
  have hc : c ≠ 0 := by
    have ha : 0 < a := h.1
    have hsum : a + b = c := h.2.2.1
    omega
  rw [abcRationalPoint_logHeight₁_eq_sum_max_zero_neg_padicValRat h,
    arithmeticPrimeSupport_abcRationalPoint h]
  refine Finset.sum_subset ?_ ?_
  · intro p hp
    have ha : 0 < a := h.1
    have hb : 0 < b := h.2.1
    exact Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp,
      dvd_trans (Nat.mem_primeFactors.mp hp).2.1 (dvd_mul_left c (a * b)),
      mul_ne_zero (mul_ne_zero (Nat.ne_of_gt ha) (Nat.ne_of_gt hb)) hc⟩
  · intro p hp hpnot
    have hp' : p.Prime := Nat.prime_of_mem_primeFactors hp
    haveI : Fact p.Prime := ⟨hp'⟩
    have hpc : padicValNat p c = 0 := padicValNat.eq_zero_of_not_dvd fun hdiv =>
      hpnot (Nat.mem_primeFactors.mpr ⟨hp', hdiv, hc⟩)
    rw [padicValRat_abcRationalPoint p h, hpc, Nat.cast_zero, sub_zero, Int.cast_natCast,
      max_eq_left (neg_nonpos.mpr (Nat.cast_nonneg (padicValNat p a))), zero_mul]

/-! ### The actual Frey/Legendre invariant `j = abcJInvariant a b c` -/

/-- Exact height of the invariant through its unreduced coordinates: the logarithm of the maximum of
`numerator / cancel` and `denominator / cancel`, where `cancel = abcInvariantCancellation`. -/
theorem abcJInvariant_logHeight₁_eq_log_max_coordinates {a b c : ℕ} (h : IsABCTriple a b c) :
    Height.logHeight₁ (abcJInvariant a b c) =
      Real.log (max ((abcInvariantNumerator a b / abcInvariantCancellation a b c : ℕ) : ℝ)
        ((abcInvariantDenominator a b c / abcInvariantCancellation a b c : ℕ) : ℝ)) := by
  rw [Rat.logHeight₁_eq_log_max, Nat.cast_max, h.abcJInvariant_num_natAbs_eq,
    h.abcJInvariant_den_eq]

/-- The archimedean logarithm of the invariant as the product-formula sum of its local
valuations. -/
theorem abcJInvariant_log_eq_sum_padicValRat {a b c : ℕ} (h : IsABCTriple a b c) :
    Real.log (abcJInvariant a b c : ℝ) =
      ∑ p ∈ (abcJInvariant a b c).num.natAbs.primeFactors ∪
          (abcJInvariant a b c).den.primeFactors,
        (padicValRat p (abcJInvariant a b c) : ℝ) * Real.log p := by
  have hjposR : (0 : ℝ) < (abcJInvariant a b c : ℝ) := by
    exact_mod_cast h.abcJInvariant_pos
  rw [← rat_log_abs_eq_sum_padicValRat (abcJInvariant a b c) h.abcJInvariant_pos.ne',
    abs_of_pos hjposR]

/-- The exact height of the invariant as the maximum of the two prime-factorization sums of its
reduced numerator and denominator. -/
theorem abcJInvariant_logHeight₁_eq_max_factorization {a b c : ℕ} (h : IsABCTriple a b c) :
    Height.logHeight₁ (abcJInvariant a b c) =
      max (∑ p ∈ (abcJInvariant a b c).num.natAbs.primeFactors,
            ((abcJInvariant a b c).num.natAbs.factorization p : ℝ) * Real.log p)
          (∑ p ∈ (abcJInvariant a b c).den.primeFactors,
            ((abcJInvariant a b c).den.factorization p : ℝ) * Real.log p) := by
  rw [Rat.logHeight₁_eq_log_max, Nat.cast_max]
  have hmaxlog : Real.log (max ((abcJInvariant a b c).num.natAbs : ℝ)
      ((abcJInvariant a b c).den : ℝ)) =
      max (Real.log ((abcJInvariant a b c).num.natAbs : ℝ))
        (Real.log ((abcJInvariant a b c).den : ℝ)) :=
    real_log_max_of_pos (by exact_mod_cast h.abcJInvariant_num_natAbs_pos)
      (by exact_mod_cast (abcJInvariant a b c).den_pos)
  rw [hmaxlog,
    real_log_nat_eq_sum_factorization (abcJInvariant a b c).num.natAbs
      h.abcJInvariant_num_natAbs_pos.ne',
    real_log_nat_eq_sum_factorization (abcJInvariant a b c).den
      (abcJInvariant a b c).den_pos.ne']

/-- The exact height of the invariant as the archimedean term `max 0 (log j)` plus the
prime-factorization sum of its denominator. -/
theorem abcJInvariant_logHeight₁_eq_archimedean_add_den_factorization {a b c : ℕ}
    (h : IsABCTriple a b c) :
    Height.logHeight₁ (abcJInvariant a b c) =
      max 0 (Real.log (abcJInvariant a b c : ℝ)) +
        ∑ p ∈ (abcJInvariant a b c).den.primeFactors,
          ((abcJInvariant a b c).den.factorization p : ℝ) * Real.log p := by
  have hjposR : (0 : ℝ) < (abcJInvariant a b c : ℝ) := by
    exact_mod_cast h.abcJInvariant_pos
  rw [rational_logHeight₁_eq_max_zero_log_abs_add_den_factorization _
    h.abcJInvariant_pos.ne', abs_of_pos hjposR]

/-- The same height with the actual local terms `max 0 (−v_p(j)) log p` of the invariant. -/
theorem abcJInvariant_logHeight₁_eq_archimedean_add_den_padicValRat {a b c : ℕ}
    (h : IsABCTriple a b c) :
    Height.logHeight₁ (abcJInvariant a b c) =
      max 0 (Real.log (abcJInvariant a b c : ℝ)) +
        ∑ p ∈ (abcJInvariant a b c).den.primeFactors,
          max 0 (-(padicValRat p (abcJInvariant a b c) : ℝ)) * Real.log p := by
  rw [abcJInvariant_logHeight₁_eq_archimedean_add_den_factorization h]
  congr 1
  exact Finset.sum_congr rfl fun p hp => by
    rw [rat_den_factorization_eq_neg_padicValRat_toNat p (Nat.prime_of_mem_primeFactors hp)
        (abcJInvariant a b c),
      int_toNat_neg_cast_eq_max_zero (padicValRat p (abcJInvariant a b c))]

/-- Full local expansion of the invariant height: the archimedean term itself expressed as the
product-formula sum of local valuations, plus the finite-valuation terms. -/
theorem abcJInvariant_logHeight₁_eq_sum_all_places {a b c : ℕ} (h : IsABCTriple a b c) :
    Height.logHeight₁ (abcJInvariant a b c) =
      max 0 (∑ p ∈ (abcJInvariant a b c).num.natAbs.primeFactors ∪
          (abcJInvariant a b c).den.primeFactors,
          (padicValRat p (abcJInvariant a b c) : ℝ) * Real.log p) +
        ∑ p ∈ (abcJInvariant a b c).den.primeFactors,
          max 0 (-(padicValRat p (abcJInvariant a b c) : ℝ)) * Real.log p :=
  rational_logHeight₁_eq_sum_all_places (abcJInvariant a b c) h.abcJInvariant_pos.ne'

/-- The denominator valuation of the invariant, in `Nat.factorization` form: `2 v_p(abc)` at odd
`p`, and the boundary value `2 v₂(abc) − 8` at the prime `2`. -/
theorem abcJInvariant_den_factorization_eq {a b c p : ℕ} (h : IsABCTriple a b c)
    (hp : p.Prime) :
    (abcJInvariant a b c).den.factorization p =
      if p = 2 then 2 * padicValNat p (a * b * c) - 8 else 2 * padicValNat p (a * b * c) := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [Nat.factorization_def (abcJInvariant a b c).den hp]
  exact h.abcJInvariant_den_padicValNat

/-- Odd-prime case of the denominator valuation. -/
theorem abcJInvariant_den_factorization_of_prime_ne_two {a b c p : ℕ} (h : IsABCTriple a b c)
    (hp : p.Prime) (hpne : p ≠ 2) :
    (abcJInvariant a b c).den.factorization p = 2 * padicValNat p (a * b * c) := by
  rw [abcJInvariant_den_factorization_eq h hp, if_neg hpne]

/-- At an odd prime dividing `abc`, the denominator valuation of the invariant is twice the total
product valuation `v_p(a) + v_p(b) + v_p(c)`. -/
theorem abcJInvariant_den_factorization_of_prime_ne_two_dvd_product {a b c p : ℕ}
    (h : IsABCTriple a b c) (hp : p.Prime) (hpne : p ≠ 2) (hdiv : p ∣ a * b * c) :
    (abcJInvariant a b c).den.factorization p =
      2 * (padicValNat p a + padicValNat p b + padicValNat p c) := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [abcJInvariant_den_factorization_of_prime_ne_two h hp hpne,
    h.abcInvariant_product_padicValNat]

/-- The denominator valuation of the invariant is the local valuation term of the invariant
itself. -/
theorem abcJInvariant_den_factorization_eq_neg_padicValRat_toNat {a b c p : ℕ}
    (h : IsABCTriple a b c) (hp : p.Prime) :
    (abcJInvariant a b c).den.factorization p =
      (-(padicValRat p (abcJInvariant a b c))).toNat :=
  rat_den_factorization_eq_neg_padicValRat_toNat p hp (abcJInvariant a b c)

/-- The numerator valuation of the invariant: the coefficient `8 [p = 2]`, three times the
valuation of `a² + ab + b²`, and the cancellation, which affects only powers of `2`. -/
theorem abcJInvariant_num_factorization_eq {a b c p : ℕ} (h : IsABCTriple a b c)
    (hp : p.Prime) :
    (abcJInvariant a b c).num.natAbs.factorization p =
      8 * padicValNat p 2 + 3 * padicValNat p (abcInvariantPolynomial a b) -
        padicValNat p (abcInvariantCancellation a b c) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hnumne : (abcJInvariant a b c).num.natAbs ≠ 0 := h.abcJInvariant_num_natAbs_pos.ne'
  have hcancelne : abcInvariantCancellation a b c ≠ 0 := h.abcInvariantCancellation_pos.ne'
  have hfact : (abcJInvariant a b c).num.natAbs.factorization p +
      (abcInvariantCancellation a b c).factorization p =
        (abcInvariantNumerator a b).factorization p := by
    have hmul := congrArg (fun n : ℕ => n.factorization p)
      h.abcJInvariant_num_natAbs_mul_cancellation
    simpa only [Nat.factorization_mul hnumne hcancelne, Finsupp.add_apply] using hmul
  rw [Nat.factorization_def (abcInvariantNumerator a b) hp,
    h.abcInvariantNumerator_padicValNat,
    Nat.factorization_def (abcInvariantCancellation a b c) hp] at hfact
  omega

/-- The `2`-adic numerator valuation of the invariant: `8 − min 8 (2 v₂(abc))`. -/
theorem abcJInvariant_num_factorization_two {a b c : ℕ} (h : IsABCTriple a b c) :
    (abcJInvariant a b c).num.natAbs.factorization 2 =
      8 - min 8 (2 * padicValNat 2 (a * b * c)) := by
  rw [abcJInvariant_num_factorization_eq h Nat.prime_two,
    padicValNat.self (by decide : 1 < (2 : ℕ)),
    h.abcInvariantPolynomial_padicValNat_two,
    h.abcInvariantCancellation_padicValNat_two]

/-- Odd-prime case of the numerator valuation: exactly three times the valuation of
`a² + ab + b²`. -/
theorem abcJInvariant_num_factorization_of_prime_ne_two {a b c p : ℕ} (h : IsABCTriple a b c)
    (hp : p.Prime) (hpne : p ≠ 2) :
    (abcJInvariant a b c).num.natAbs.factorization p =
      3 * padicValNat p (abcInvariantPolynomial a b) := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [abcJInvariant_num_factorization_eq h hp,
    abcInvariant_prime_ne_two_padicValNat_two hpne,
    h.abcInvariantCancellation_padicValNat_of_prime_ne_two hpne]
  omega

/-- At an odd prime dividing `abc` the numerator of the invariant is valuation-free: the polynomial
`a² + ab + b²` is coprime to `abc`. -/
theorem abcJInvariant_num_factorization_eq_zero_of_prime_ne_two_dvd_product {a b c p : ℕ}
    (h : IsABCTriple a b c) (hp : p.Prime) (hpne : p ≠ 2) (hdiv : p ∣ a * b * c) :
    (abcJInvariant a b c).num.natAbs.factorization p = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [abcJInvariant_num_factorization_of_prime_ne_two h hp hpne,
    h.abcInvariantPolynomial_padicValNat_eq_zero_of_dvd_product hdiv]

end LeanFormal.IUT