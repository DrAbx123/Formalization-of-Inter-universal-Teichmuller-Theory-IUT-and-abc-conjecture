import LeanFormal.IUT.ABCBridge.Arithmetic.ABCInvariantCoprimality
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
Actual rational p-adic valuations of the ABC Frey/Legendre expression.

The denominator support agrees with that of `abc` away from 2. At 2 the
valuation is `8 - 2 * v₂(abc)`, so a denominator occurs precisely when
`v₂(abc) ≥ 5`. These statements concern the rational j-expression and its
reduced denominator. They do not identify a minimal model or its conductor.
-/

namespace LeanFormal.IUT

theorem IsABCTriple.abcInvariantPolynomial_mod_two {a b c : ℕ}
    (h : IsABCTriple a b c) : abcInvariantPolynomial a b % 2 = 1 := by
  have hnotboth : ¬(a % 2 = 0 ∧ b % 2 = 0) := by
    rintro ⟨ha, hb⟩
    have hcommon : 2 ∣ Nat.gcd a b := Nat.dvd_gcd
      (Nat.dvd_of_mod_eq_zero ha) (Nat.dvd_of_mod_eq_zero hb)
    rw [h.2.2.2.gcd_eq_one] at hcommon
    norm_num at hcommon
  have hamod : a % 2 = 0 ∨ a % 2 = 1 := by omega
  have hbmod : b % 2 = 0 ∨ b % 2 = 1 := by omega
  rcases hamod with ha | ha <;> rcases hbmod with hb | hb
  · exact False.elim (hnotboth ⟨ha, hb⟩)
  · norm_num [abcInvariantPolynomial, Nat.add_mod, Nat.mul_mod, Nat.pow_mod, ha, hb]
  · norm_num [abcInvariantPolynomial, Nat.add_mod, Nat.mul_mod, Nat.pow_mod, ha, hb]
  · norm_num [abcInvariantPolynomial, Nat.add_mod, Nat.mul_mod, Nat.pow_mod, ha, hb]

theorem IsABCTriple.abcInvariantPolynomial_odd {a b c : ℕ}
    (h : IsABCTriple a b c) : Odd (abcInvariantPolynomial a b) := by
  exact Nat.odd_iff.mpr h.abcInvariantPolynomial_mod_two

theorem IsABCTriple.two_not_dvd_abcInvariantPolynomial {a b c : ℕ}
    (h : IsABCTriple a b c) : ¬2 ∣ abcInvariantPolynomial a b := by
  intro hdiv
  have hzero := Nat.mod_eq_zero_of_dvd hdiv
  have hone := h.abcInvariantPolynomial_mod_two
  omega

theorem IsABCTriple.abcInvariant_product_pos {a b c : ℕ}
    (h : IsABCTriple a b c) : 0 < a * b * c := by
  have hcpos : 0 < c := by
    have hapos := h.1
    have hsum := h.2.2.1
    omega
  exact Nat.mul_pos (Nat.mul_pos h.1 h.2.1) hcpos

theorem IsABCTriple.two_dvd_abcInvariant_product {a b c : ℕ}
    (h : IsABCTriple a b c) : 2 ∣ a * b * c := by
  apply Nat.dvd_of_mod_eq_zero
  rw [← h.2.2.1]
  have hamod : a % 2 = 0 ∨ a % 2 = 1 := by omega
  have hbmod : b % 2 = 0 ∨ b % 2 = 1 := by omega
  rcases hamod with ha | ha <;> rcases hbmod with hb | hb <;>
    norm_num [Nat.add_mod, Nat.mul_mod, ha, hb]

theorem IsABCTriple.prime_not_dvd_abcInvariantPolynomial_of_dvd_product
    {a b c p : ℕ} (h : IsABCTriple a b c) [Fact p.Prime]
    (hdiv : p ∣ a * b * c) : ¬p ∣ abcInvariantPolynomial a b := by
  intro hpoly
  have hone : p ∣ 1 := by
    rw [← h.abcInvariantPolynomial_coprime_product.gcd_eq_one]
    exact Nat.dvd_gcd hpoly hdiv
  exact (Fact.out : p.Prime).ne_one (Nat.eq_one_of_dvd_one hone)

theorem IsABCTriple.abcInvariantPolynomial_padicValNat_eq_zero_of_dvd_product
    {a b c p : ℕ} (h : IsABCTriple a b c) [Fact p.Prime]
    (hdiv : p ∣ a * b * c) : padicValNat p (abcInvariantPolynomial a b) = 0 := by
  exact padicValNat.eq_zero_of_not_dvd
    (h.prime_not_dvd_abcInvariantPolynomial_of_dvd_product hdiv)

theorem IsABCTriple.abcInvariantPolynomial_padicValNat_two {a b c : ℕ}
    (h : IsABCTriple a b c) : padicValNat 2 (abcInvariantPolynomial a b) = 0 := by
  exact padicValNat.eq_zero_of_not_dvd h.two_not_dvd_abcInvariantPolynomial

theorem abcInvariant_prime_ne_two_padicValNat_two {p : ℕ} [Fact p.Prime]
    (hpne : p ≠ 2) : padicValNat p 2 = 0 := by
  apply padicValNat.eq_zero_of_not_dvd
  intro hdiv
  have hle : p ≤ 2 := Nat.le_of_dvd (by decide) hdiv
  have hge : 2 ≤ p := (Fact.out : p.Prime).two_le
  omega

theorem abcInvariant_coefficient_padicValNat (p : ℕ) [Fact p.Prime] :
    padicValNat p 256 = 8 * padicValNat p 2 := by
  have hpower : (256 : ℕ) = 2 ^ 8 := by norm_num
  rw [hpower, padicValNat.pow]

theorem IsABCTriple.abcInvariant_product_padicValNat {a b c p : ℕ}
    (h : IsABCTriple a b c) [Fact p.Prime] :
    padicValNat p (a * b * c) = padicValNat p a + padicValNat p b + padicValNat p c := by
  have hane : a ≠ 0 := Nat.ne_of_gt h.1
  have hbne : b ≠ 0 := Nat.ne_of_gt h.2.1
  have hcne : c ≠ 0 := by
    have hproduct := h.abcInvariant_product_pos
    intro hzero
    simp [hzero] at hproduct
  rw [padicValNat.mul (mul_ne_zero hane hbne) hcne, padicValNat.mul hane hbne]

theorem IsABCTriple.abcInvariantNumerator_padicValNat {a b c p : ℕ}
    (h : IsABCTriple a b c) [Fact p.Prime] :
    padicValNat p (abcInvariantNumerator a b) =
      8 * padicValNat p 2 + 3 * padicValNat p (abcInvariantPolynomial a b) := by
  have hpolyne : abcInvariantPolynomial a b ≠ 0 :=
    Nat.ne_of_gt h.abcInvariantPolynomial_pos
  unfold abcInvariantNumerator
  rw [padicValNat.mul (by norm_num) (pow_ne_zero 3 hpolyne),
    abcInvariant_coefficient_padicValNat, padicValNat.pow]

theorem abcInvariantDenominator_padicValNat (a b c p : ℕ) [Fact p.Prime] :
    padicValNat p (abcInvariantDenominator a b c) = 2 * padicValNat p (a * b * c) := by
  rw [abcInvariantDenominator_eq_product_square, padicValNat.pow]

theorem IsABCTriple.abcJInvariant_padicValRat {a b c p : ℕ}
    (h : IsABCTriple a b c) [Fact p.Prime] :
    padicValRat p (abcJInvariant a b c) =
      8 * (padicValNat p 2 : ℤ) + 3 * (padicValNat p (abcInvariantPolynomial a b) : ℤ) -
        2 * (padicValNat p (a * b * c) : ℤ) := by
  have hnumne : (abcInvariantNumerator a b : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt h.abcInvariantNumerator_pos
  have hdenne : (abcInvariantDenominator a b c : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt h.abcInvariantDenominator_pos
  unfold abcJInvariant
  rw [padicValRat.div hnumne hdenne, padicValRat.of_nat, padicValRat.of_nat,
    h.abcInvariantNumerator_padicValNat, abcInvariantDenominator_padicValNat]
  push_cast <;> ring

theorem IsABCTriple.abcJInvariant_padicValRat_of_prime_ne_two
    {a b c p : ℕ} (h : IsABCTriple a b c) [Fact p.Prime] (hpne : p ≠ 2) :
    padicValRat p (abcJInvariant a b c) =
      3 * (padicValNat p (abcInvariantPolynomial a b) : ℤ) -
        2 * (padicValNat p (a * b * c) : ℤ) := by
  rw [h.abcJInvariant_padicValRat, abcInvariant_prime_ne_two_padicValNat_two hpne]
  simp

theorem IsABCTriple.abcJInvariant_padicValRat_of_prime_ne_two_dvd_product
    {a b c p : ℕ} (h : IsABCTriple a b c) [Fact p.Prime]
    (hpne : p ≠ 2) (hdiv : p ∣ a * b * c) :
    padicValRat p (abcJInvariant a b c) = -2 * (padicValNat p (a * b * c) : ℤ) := by
  rw [h.abcJInvariant_padicValRat_of_prime_ne_two hpne,
    h.abcInvariantPolynomial_padicValNat_eq_zero_of_dvd_product hdiv]
  simp <;> ring

theorem IsABCTriple.abcJInvariant_padicValRat_of_prime_ne_two_dvd_product_sum
    {a b c p : ℕ} (h : IsABCTriple a b c) [Fact p.Prime]
    (hpne : p ≠ 2) (hdiv : p ∣ a * b * c) :
    padicValRat p (abcJInvariant a b c) =
      -2 * ((padicValNat p a : ℤ) + (padicValNat p b : ℤ) + (padicValNat p c : ℤ)) := by
  rw [h.abcJInvariant_padicValRat_of_prime_ne_two_dvd_product hpne hdiv,
    h.abcInvariant_product_padicValNat]
  push_cast <;> rfl

theorem IsABCTriple.abcJInvariant_padicValRat_of_prime_ne_two_not_dvd_product
    {a b c p : ℕ} (h : IsABCTriple a b c) [Fact p.Prime]
    (hpne : p ≠ 2) (hnotdiv : ¬p ∣ a * b * c) :
    padicValRat p (abcJInvariant a b c) =
      3 * (padicValNat p (abcInvariantPolynomial a b) : ℤ) := by
  rw [h.abcJInvariant_padicValRat_of_prime_ne_two hpne,
    padicValNat.eq_zero_of_not_dvd hnotdiv]
  simp

theorem IsABCTriple.abcJInvariant_padicValRat_nonneg_of_not_dvd_product
    {a b c p : ℕ} (h : IsABCTriple a b c) [Fact p.Prime]
    (hnotdiv : ¬p ∣ a * b * c) : 0 ≤ padicValRat p (abcJInvariant a b c) := by
  rw [h.abcJInvariant_padicValRat, padicValNat.eq_zero_of_not_dvd hnotdiv]
  simp only [Nat.cast_zero, mul_zero, sub_zero]
  positivity

theorem IsABCTriple.abcJInvariant_padicValRat_two {a b c : ℕ}
    (h : IsABCTriple a b c) :
    padicValRat 2 (abcJInvariant a b c) = 8 - 2 * (padicValNat 2 (a * b * c) : ℤ) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [h.abcJInvariant_padicValRat, h.abcInvariantPolynomial_padicValNat_two,
    padicValNat.self (by decide : 1 < (2 : ℕ))]
  norm_num

theorem IsABCTriple.abcJInvariant_padicValRat_two_sum {a b c : ℕ}
    (h : IsABCTriple a b c) :
    padicValRat 2 (abcJInvariant a b c) =
      8 - 2 * ((padicValNat 2 a : ℤ) + (padicValNat 2 b : ℤ) + (padicValNat 2 c : ℤ)) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [h.abcJInvariant_padicValRat_two, h.abcInvariant_product_padicValNat]
  push_cast <;> rfl

theorem rational_den_padicValNat_eq_neg_padicValRat_toNat
    (p : ℕ) [Fact p.Prime] (q : ℚ) :
    padicValNat p q.den = (-padicValRat p q).toNat := by
  have hvaluation : padicValRat p q =
      (padicValNat p q.num.natAbs : ℤ) - (padicValNat p q.den : ℤ) := by
    exact padicValRat.eq_1 p q
  by_cases hnumdiv : p ∣ q.num.natAbs
  · have hdennotdiv : ¬p ∣ q.den := by
      intro hdendiv
      have hone : p ∣ 1 := by
        rw [← q.reduced.gcd_eq_one]
        exact Nat.dvd_gcd hnumdiv hdendiv
      exact (Fact.out : p.Prime).ne_one (Nat.eq_one_of_dvd_one hone)
    have hdenzero := padicValNat.eq_zero_of_not_dvd hdennotdiv
    rw [hdenzero, hvaluation, hdenzero]
    omega
  · have hnumzero := padicValNat.eq_zero_of_not_dvd hnumdiv
    rw [hvaluation, hnumzero]
    simp

theorem abcInvariant_prime_dvd_iff_padicValNat_pos
    {p n : ℕ} [Fact p.Prime] (hnpos : 0 < n) : p ∣ n ↔ 0 < padicValNat p n := by
  constructor
  · intro hdiv
    by_contra hnotpos
    have hzero : padicValNat p n = 0 := by omega
    rcases padicValNat.eq_zero_iff.mp hzero with hpone | hnzero | hnotdiv
    · exact (Fact.out : p.Prime).ne_one hpone
    · exact (Nat.ne_of_gt hnpos) hnzero
    · exact hnotdiv hdiv
  · intro hpos
    by_contra hnotdiv
    have hzero := padicValNat.eq_zero_of_not_dvd hnotdiv
    omega

theorem rational_prime_dvd_den_iff_padicValRat_neg
    (p : ℕ) [Fact p.Prime] (q : ℚ) : p ∣ q.den ↔ padicValRat p q < 0 := by
  rw [abcInvariant_prime_dvd_iff_padicValNat_pos q.den_pos,
    rational_den_padicValNat_eq_neg_padicValRat_toNat]
  omega

theorem IsABCTriple.abcJInvariant_den_padicValNat_of_prime_ne_two
    {a b c p : ℕ} (h : IsABCTriple a b c) [Fact p.Prime] (hpne : p ≠ 2) :
    padicValNat p (abcJInvariant a b c).den = 2 * padicValNat p (a * b * c) := by
  have hden := rational_den_padicValNat_eq_neg_padicValRat_toNat p (abcJInvariant a b c)
  by_cases hdiv : p ∣ a * b * c
  · rw [h.abcJInvariant_padicValRat_of_prime_ne_two_dvd_product hpne hdiv] at hden
    omega
  · have hproductzero := padicValNat.eq_zero_of_not_dvd hdiv
    have hnonneg := h.abcJInvariant_padicValRat_nonneg_of_not_dvd_product hdiv
    omega

theorem IsABCTriple.abcJInvariant_den_padicValNat_two {a b c : ℕ}
    (h : IsABCTriple a b c) :
    padicValNat 2 (abcJInvariant a b c).den = 2 * padicValNat 2 (a * b * c) - 8 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hden := rational_den_padicValNat_eq_neg_padicValRat_toNat 2 (abcJInvariant a b c)
  rw [h.abcJInvariant_padicValRat_two] at hden
  omega

theorem IsABCTriple.abcJInvariant_den_padicValNat_two_int {a b c : ℕ}
    (h : IsABCTriple a b c) :
    (padicValNat 2 (abcJInvariant a b c).den : ℤ) =
      max 0 (2 * (padicValNat 2 (a * b * c) : ℤ) - 8) := by
  rw [h.abcJInvariant_den_padicValNat_two]
  omega

theorem IsABCTriple.abcJInvariant_den_padicValNat {a b c p : ℕ}
    (h : IsABCTriple a b c) [Fact p.Prime] :
    padicValNat p (abcJInvariant a b c).den =
      if p = 2 then 2 * padicValNat p (a * b * c) - 8
      else 2 * padicValNat p (a * b * c) := by
  by_cases hp : p = 2
  · subst p
    simpa using h.abcJInvariant_den_padicValNat_two
  · simpa [hp] using h.abcJInvariant_den_padicValNat_of_prime_ne_two hp

theorem IsABCTriple.prime_ne_two_dvd_abcJInvariant_den_iff
    {a b c p : ℕ} (h : IsABCTriple a b c) [Fact p.Prime] (hpne : p ≠ 2) :
    p ∣ (abcJInvariant a b c).den ↔ p ∣ a * b * c := by
  rw [abcInvariant_prime_dvd_iff_padicValNat_pos (abcJInvariant a b c).den_pos,
    abcInvariant_prime_dvd_iff_padicValNat_pos h.abcInvariant_product_pos,
    h.abcJInvariant_den_padicValNat_of_prime_ne_two hpne]
  omega

theorem IsABCTriple.two_dvd_abcJInvariant_den_iff {a b c : ℕ}
    (h : IsABCTriple a b c) :
    2 ∣ (abcJInvariant a b c).den ↔ 5 ≤ padicValNat 2 (a * b * c) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [abcInvariant_prime_dvd_iff_padicValNat_pos (abcJInvariant a b c).den_pos,
    h.abcJInvariant_den_padicValNat_two]
  omega

theorem IsABCTriple.prime_dvd_abcJInvariant_den_iff {a b c p : ℕ}
    (h : IsABCTriple a b c) [Fact p.Prime] :
    p ∣ (abcJInvariant a b c).den ↔
      (p ≠ 2 ∧ p ∣ a * b * c) ∨ (p = 2 ∧ 5 ≤ padicValNat 2 (a * b * c)) := by
  by_cases hp : p = 2
  · subst p
    simpa using h.two_dvd_abcJInvariant_den_iff
  · simpa [hp] using h.prime_ne_two_dvd_abcJInvariant_den_iff hp

theorem IsABCTriple.prime_dvd_product_of_dvd_abcJInvariant_den
    {a b c p : ℕ} (h : IsABCTriple a b c) [Fact p.Prime]
    (hdiv : p ∣ (abcJInvariant a b c).den) : p ∣ a * b * c := by
  by_cases hp : p = 2
  · simpa [hp] using h.two_dvd_abcInvariant_product
  · exact (h.prime_ne_two_dvd_abcJInvariant_den_iff hp).mp hdiv

theorem IsABCTriple.prime_dvd_product_iff_two_or_dvd_abcJInvariant_den
    {a b c p : ℕ} (h : IsABCTriple a b c) [Fact p.Prime] :
    p ∣ a * b * c ↔ p = 2 ∨ p ∣ (abcJInvariant a b c).den := by
  constructor
  · intro hdiv
    by_cases hp : p = 2
    · exact Or.inl hp
    · exact Or.inr ((h.prime_ne_two_dvd_abcJInvariant_den_iff hp).mpr hdiv)
  · rintro (hp | hdiv)
    · simpa [hp] using h.two_dvd_abcInvariant_product
    · exact h.prime_dvd_product_of_dvd_abcJInvariant_den hdiv

theorem IsABCTriple.prime_dvd_twice_abcJInvariant_den_iff
    {a b c p : ℕ} (h : IsABCTriple a b c) [Fact p.Prime] :
    p ∣ 2 * (abcJInvariant a b c).den ↔ p ∣ a * b * c := by
  rw [(Fact.out : p.Prime).dvd_mul,
    h.prime_dvd_product_iff_two_or_dvd_abcJInvariant_den]
  have hdivtwo : p ∣ 2 ↔ p = 2 := by
    constructor
    · intro hdiv
      have hle : p ≤ 2 := Nat.le_of_dvd (by decide) hdiv
      have hge : 2 ≤ p := (Fact.out : p.Prime).two_le
      omega
    · intro hp
      simpa [hp]
  rw [hdivtwo]

theorem IsABCTriple.abcJInvariant_padicValRat_neg_iff
    {a b c p : ℕ} (h : IsABCTriple a b c) [Fact p.Prime] :
    padicValRat p (abcJInvariant a b c) < 0 ↔
      (p ≠ 2 ∧ p ∣ a * b * c) ∨ (p = 2 ∧ 5 ≤ padicValNat 2 (a * b * c)) := by
  rw [← rational_prime_dvd_den_iff_padicValRat_neg,
    h.prime_dvd_abcJInvariant_den_iff]

theorem IsABCTriple.abcJInvariant_padicValRat_two_nonneg_iff {a b c : ℕ}
    (h : IsABCTriple a b c) :
    0 ≤ padicValRat 2 (abcJInvariant a b c) ↔ padicValNat 2 (a * b * c) ≤ 4 := by
  rw [h.abcJInvariant_padicValRat_two]
  omega

theorem IsABCTriple.abcInvariantCancellation_padicValNat_of_prime_ne_two
    {a b c p : ℕ} (h : IsABCTriple a b c) [Fact p.Prime] (hpne : p ≠ 2) :
    padicValNat p (abcInvariantCancellation a b c) = 0 := by
  apply padicValNat.eq_zero_of_not_dvd
  intro hdiv
  have hdiv256 : p ∣ 256 := dvd_trans hdiv h.abcInvariantCancellation_dvd_256
  have hdivpow : p ∣ 2 ^ 8 := by
    simpa only [show (2 : ℕ) ^ 8 = 256 by norm_num] using hdiv256
  have hdivtwo : p ∣ 2 := (Fact.out : p.Prime).dvd_of_dvd_pow hdivpow
  have hle : p ≤ 2 := Nat.le_of_dvd (by decide) hdivtwo
  have hge : 2 ≤ p := (Fact.out : p.Prime).two_le
  omega

theorem IsABCTriple.abcInvariantCancellation_padicValNat_two {a b c : ℕ}
    (h : IsABCTriple a b c) :
    padicValNat 2 (abcInvariantCancellation a b c) =
      min 8 (2 * padicValNat 2 (a * b * c)) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcancel := congrArg (padicValNat 2) h.abcJInvariant_den_mul_cancellation
  rw [padicValNat.mul (abcJInvariant a b c).den_nz
    (Nat.ne_of_gt h.abcInvariantCancellation_pos),
    abcInvariantDenominator_padicValNat, h.abcJInvariant_den_padicValNat_two] at hcancel
  omega

theorem IsABCTriple.abcInvariantCancellation_padicValNat {a b c p : ℕ}
    (h : IsABCTriple a b c) [Fact p.Prime] :
    padicValNat p (abcInvariantCancellation a b c) =
      if p = 2 then min 8 (2 * padicValNat p (a * b * c)) else 0 := by
  by_cases hp : p = 2
  · subst p
    simpa using h.abcInvariantCancellation_padicValNat_two
  · simpa [hp] using h.abcInvariantCancellation_padicValNat_of_prime_ne_two hp

end LeanFormal.IUT
