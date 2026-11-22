import LeanFormal.IUT.ABCBridge.Arithmetic.PrimitiveTriple

/-!
Cancellation in the rational Frey/Legendre invariant attached to an ABC triple.

The polynomial `a² + ab + b²` is prime to the product `abc` for a primitive
positive triple with `a + b = c`. Consequently the only cancellation in
`256 * (a² + ab + b²)³ / (a² * b² * c²)` comes from the fixed coefficient 256.
The reduced numerator and denominator below use the actual `Rat` projections.
These are arithmetic inputs for a height comparison; no IUT specialization is
asserted here.
-/

namespace LeanFormal.IUT

def abcInvariantPolynomial (a b : ℕ) : ℕ := a ^ 2 + a * b + b ^ 2

def abcInvariantNumerator (a b : ℕ) : ℕ := 256 * abcInvariantPolynomial a b ^ 3

def abcInvariantDenominator (a b c : ℕ) : ℕ := a ^ 2 * b ^ 2 * c ^ 2

def abcInvariantCancellation (a b c : ℕ) : ℕ :=
  Nat.gcd (abcInvariantNumerator a b) (abcInvariantDenominator a b c)

def abcJInvariant (a b c : ℕ) : ℚ :=
  (abcInvariantNumerator a b : ℚ) / (abcInvariantDenominator a b c : ℚ)

theorem IsABCTriple.abcInvariantPolynomial_pos {a b c : ℕ}
    (h : IsABCTriple a b c) : 0 < abcInvariantPolynomial a b := by
  dsimp [abcInvariantPolynomial]
  have hapos : 0 < a ^ 2 := pow_pos h.1 2
  omega

theorem IsABCTriple.abcInvariantPolynomial_add_product {a b c : ℕ}
    (h : IsABCTriple a b c) : abcInvariantPolynomial a b + a * b = c ^ 2 := by
  rw [← h.2.2.1]
  dsimp [abcInvariantPolynomial]
  ring

theorem IsABCTriple.abcInvariantPolynomial_coprime_left {a b c : ℕ}
    (h : IsABCTriple a b c) : Nat.Coprime (abcInvariantPolynomial a b) a := by
  have hcoprime : Nat.Coprime (b ^ 2) a := h.2.2.2.symm.pow_left 2
  have hsum : abcInvariantPolynomial a b = b ^ 2 + a * (a + b) := by
    dsimp [abcInvariantPolynomial]
    ring
  rw [hsum]
  exact (Nat.coprime_add_mul_left_left (b ^ 2) a (a + b)).mpr hcoprime

theorem IsABCTriple.abcInvariantPolynomial_coprime_right {a b c : ℕ}
    (h : IsABCTriple a b c) : Nat.Coprime (abcInvariantPolynomial a b) b := by
  have hcoprime : Nat.Coprime (a ^ 2) b := h.2.2.2.pow_left 2
  have hsum : abcInvariantPolynomial a b = a ^ 2 + b * (a + b) := by
    dsimp [abcInvariantPolynomial]
    ring
  rw [hsum]
  exact (Nat.coprime_add_mul_left_left (a ^ 2) b (a + b)).mpr hcoprime

theorem IsABCTriple.abcInvariantPolynomial_coprime_sum {a b c : ℕ}
    (h : IsABCTriple a b c) : Nat.Coprime (abcInvariantPolynomial a b) c := by
  have hproduct : Nat.Coprime (a * b) c :=
    h.coprime_left_right.mul_left h.coprime_right_left
  let common := Nat.gcd (abcInvariantPolynomial a b) c
  have hcommon_poly : common ∣ abcInvariantPolynomial a b := Nat.gcd_dvd_left _ _
  have hcommon_c : common ∣ c := Nat.gcd_dvd_right _ _
  have hcommon_square : common ∣ c ^ 2 := by
    exact dvd_trans hcommon_c (by exact ⟨c, by ring⟩)
  have hcommon_product : common ∣ a * b := by
    apply (Nat.dvd_add_iff_right hcommon_poly).mpr
    rw [h.abcInvariantPolynomial_add_product]
    exact hcommon_square
  have hcommon_one : common ∣ 1 := by
    rw [← hproduct.gcd_eq_one]
    exact Nat.dvd_gcd hcommon_product hcommon_c
  exact Nat.eq_one_of_dvd_one hcommon_one

theorem IsABCTriple.abcInvariantPolynomial_coprime_product {a b c : ℕ}
    (h : IsABCTriple a b c) :
    Nat.Coprime (abcInvariantPolynomial a b) (a * b * c) := by
  exact (h.abcInvariantPolynomial_coprime_left.mul_right
    h.abcInvariantPolynomial_coprime_right).mul_right
      h.abcInvariantPolynomial_coprime_sum

theorem abcInvariantDenominator_eq_product_square (a b c : ℕ) :
    abcInvariantDenominator a b c = (a * b * c) ^ 2 := by
  dsimp [abcInvariantDenominator]
  ring

theorem IsABCTriple.abcInvariantPolynomial_pow_coprime_product_pow
    {a b c : ℕ} (h : IsABCTriple a b c) (polynomialExponent productExponent : ℕ) :
    Nat.Coprime (abcInvariantPolynomial a b ^ polynomialExponent)
      ((a * b * c) ^ productExponent) := by
  exact (h.abcInvariantPolynomial_coprime_product.pow_left polynomialExponent).pow_right
    productExponent

theorem IsABCTriple.abcInvariantPolynomial_cube_coprime_denominator
    {a b c : ℕ} (h : IsABCTriple a b c) :
    Nat.Coprime (abcInvariantPolynomial a b ^ 3) (abcInvariantDenominator a b c) := by
  rw [abcInvariantDenominator_eq_product_square]
  exact h.abcInvariantPolynomial_pow_coprime_product_pow 3 2

theorem IsABCTriple.abcInvariantNumerator_pos {a b c : ℕ}
    (h : IsABCTriple a b c) : 0 < abcInvariantNumerator a b := by
  exact Nat.mul_pos (by decide) (pow_pos h.abcInvariantPolynomial_pos 3)

theorem IsABCTriple.abcInvariantDenominator_pos {a b c : ℕ}
    (h : IsABCTriple a b c) : 0 < abcInvariantDenominator a b c := by
  have hcpos : 0 < c := by
    have hapos := h.1
    have hsum := h.2.2.1
    omega
  exact Nat.mul_pos (Nat.mul_pos (pow_pos h.1 2) (pow_pos h.2.1 2)) (pow_pos hcpos 2)

theorem IsABCTriple.abcInvariantCancellation_eq_gcd_coefficient
    {a b c : ℕ} (h : IsABCTriple a b c) :
    abcInvariantCancellation a b c = Nat.gcd 256 (abcInvariantDenominator a b c) := by
  exact h.abcInvariantPolynomial_cube_coprime_denominator.gcd_mul_right_cancel 256

theorem IsABCTriple.abcInvariantCancellation_dvd_256 {a b c : ℕ}
    (h : IsABCTriple a b c) : abcInvariantCancellation a b c ∣ 256 := by
  rw [h.abcInvariantCancellation_eq_gcd_coefficient]
  exact Nat.gcd_dvd_left _ _

theorem IsABCTriple.abcInvariantCancellation_pos {a b c : ℕ}
    (h : IsABCTriple a b c) : 0 < abcInvariantCancellation a b c := by
  exact Nat.gcd_pos_of_pos_right _ h.abcInvariantDenominator_pos

theorem IsABCTriple.abcInvariantCancellation_le_256 {a b c : ℕ}
    (h : IsABCTriple a b c) : abcInvariantCancellation a b c ≤ 256 := by
  exact Nat.le_of_dvd (by decide) h.abcInvariantCancellation_dvd_256

theorem abcInvariantCancellation_dvd_numerator (a b c : ℕ) :
    abcInvariantCancellation a b c ∣ abcInvariantNumerator a b := by
  exact Nat.gcd_dvd_left _ _

theorem abcInvariantCancellation_dvd_denominator (a b c : ℕ) :
    abcInvariantCancellation a b c ∣ abcInvariantDenominator a b c := by
  exact Nat.gcd_dvd_right _ _

theorem IsABCTriple.abcJInvariant_pos {a b c : ℕ}
    (h : IsABCTriple a b c) : 0 < abcJInvariant a b c := by
  exact div_pos (by exact_mod_cast h.abcInvariantNumerator_pos)
    (by exact_mod_cast h.abcInvariantDenominator_pos)

theorem abcJInvariant_eq_mkRat (a b c : ℕ) :
    abcJInvariant a b c = mkRat (abcInvariantNumerator a b : ℤ)
      (abcInvariantDenominator a b c) := by
  rw [Rat.mkRat_eq_div]
  simp [abcJInvariant]

theorem IsABCTriple.abcJInvariant_num_eq {a b c : ℕ}
    (h : IsABCTriple a b c) :
    (abcJInvariant a b c).num =
      ((abcInvariantNumerator a b / abcInvariantCancellation a b c : ℕ) : ℤ) := by
  rw [abcJInvariant_eq_mkRat, Rat.num_mkRat]
  simp only [Nat.ne_of_gt h.abcInvariantDenominator_pos, ↓reduceIte,
    Int.natAbs_natCast, ← Int.natCast_ediv, abcInvariantCancellation, Nat.gcd_comm]

theorem IsABCTriple.abcJInvariant_num_natAbs_eq {a b c : ℕ}
    (h : IsABCTriple a b c) :
    (abcJInvariant a b c).num.natAbs =
      abcInvariantNumerator a b / abcInvariantCancellation a b c := by
  rw [h.abcJInvariant_num_eq]
  exact Int.natAbs_natCast _

theorem IsABCTriple.abcJInvariant_den_eq {a b c : ℕ}
    (h : IsABCTriple a b c) :
    (abcJInvariant a b c).den =
      abcInvariantDenominator a b c / abcInvariantCancellation a b c := by
  rw [abcJInvariant_eq_mkRat, Rat.den_mkRat]
  simp only [Nat.ne_of_gt h.abcInvariantDenominator_pos, ↓reduceIte,
    Int.natAbs_natCast, abcInvariantCancellation, Nat.gcd_comm]

theorem IsABCTriple.abcJInvariant_num_pos {a b c : ℕ}
    (h : IsABCTriple a b c) : 0 < (abcJInvariant a b c).num := by
  exact Rat.num_pos.mpr h.abcJInvariant_pos

theorem IsABCTriple.abcJInvariant_num_natAbs_pos {a b c : ℕ}
    (h : IsABCTriple a b c) : 0 < (abcJInvariant a b c).num.natAbs := by
  rw [h.abcJInvariant_num_natAbs_eq]
  exact Nat.div_pos
    (Nat.le_of_dvd h.abcInvariantNumerator_pos
      (abcInvariantCancellation_dvd_numerator a b c))
    h.abcInvariantCancellation_pos

theorem IsABCTriple.abcJInvariant_reduced_coprime {a b c : ℕ}
    (h : IsABCTriple a b c) :
    Nat.Coprime (abcInvariantNumerator a b / abcInvariantCancellation a b c)
      (abcInvariantDenominator a b c / abcInvariantCancellation a b c) := by
  exact Nat.coprime_div_gcd_div_gcd h.abcInvariantCancellation_pos

theorem IsABCTriple.abcJInvariant_num_natAbs_mul_cancellation {a b c : ℕ}
    (h : IsABCTriple a b c) :
    (abcJInvariant a b c).num.natAbs * abcInvariantCancellation a b c =
      abcInvariantNumerator a b := by
  rw [h.abcJInvariant_num_natAbs_eq]
  exact Nat.div_mul_cancel (abcInvariantCancellation_dvd_numerator a b c)

theorem IsABCTriple.abcJInvariant_den_mul_cancellation {a b c : ℕ}
    (h : IsABCTriple a b c) :
    (abcJInvariant a b c).den * abcInvariantCancellation a b c =
      abcInvariantDenominator a b c := by
  rw [h.abcJInvariant_den_eq]
  exact Nat.div_mul_cancel (abcInvariantCancellation_dvd_denominator a b c)

theorem IsABCTriple.abcJInvariant_num_natAbs_le_numerator {a b c : ℕ}
    (h : IsABCTriple a b c) :
    (abcJInvariant a b c).num.natAbs ≤ abcInvariantNumerator a b := by
  rw [h.abcJInvariant_num_natAbs_eq]
  exact Nat.div_le_self _ _

theorem IsABCTriple.abcJInvariant_den_le_denominator {a b c : ℕ}
    (h : IsABCTriple a b c) :
    (abcJInvariant a b c).den ≤ abcInvariantDenominator a b c := by
  rw [h.abcJInvariant_den_eq]
  exact Nat.div_le_self _ _

theorem IsABCTriple.abcJInvariant_den_mul_256_ge_denominator {a b c : ℕ}
    (h : IsABCTriple a b c) :
    abcInvariantDenominator a b c ≤ (abcJInvariant a b c).den * 256 := by
  rw [← h.abcJInvariant_den_mul_cancellation]
  exact Nat.mul_le_mul_left _ h.abcInvariantCancellation_le_256

theorem IsABCTriple.abcJInvariant_num_natAbs_ge_polynomial_cube {a b c : ℕ}
    (h : IsABCTriple a b c) :
    abcInvariantPolynomial a b ^ 3 ≤ (abcJInvariant a b c).num.natAbs := by
  have hcancel := h.abcJInvariant_num_natAbs_mul_cancellation
  have hbound := Nat.mul_le_mul_left (abcJInvariant a b c).num.natAbs
    h.abcInvariantCancellation_le_256
  dsimp [abcInvariantNumerator] at hcancel
  omega

end LeanFormal.IUT
