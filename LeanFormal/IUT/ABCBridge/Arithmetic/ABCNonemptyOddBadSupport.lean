import LeanFormal.IUT.ABCBridge.Arithmetic.ABCInvariantRadicalBridge
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
The single ABC triple without an odd prime in the support of its product.

For an actual primitive positive ABC triple, this exception is `(1,1,2)`.
Every other triple therefore supplies an odd prime dividing the actual
reduced j-denominator, and the rational p-adic valuation at that prime is
negative. The finite support and its selected element are arithmetic input
for an odd-prime local Tate argument. No identification with a paper-specific
selected-bad set or with every place of bad reduction is made here.
-/

namespace LeanFormal.IUT

theorem positive_nat_eq_two_pow_of_only_two_prime_divisors
    (n : ℕ) (hnpos : 0 < n)
    (hsupport : ∀ p : ℕ, p.Prime → p ∣ n → p = 2) : ∃ k : ℕ, n = 2 ^ k := by
  revert hnpos hsupport
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hnpos hsupport
    by_cases hnone : n = 1
    · exact ⟨0, by simpa using hnone⟩
    obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd hnone
    have hp2 : p = 2 := hsupport p hp hpn
    have htwodiv : 2 ∣ n := by simpa [hp2] using hpn
    obtain ⟨m, hnm⟩ := htwodiv
    have hmpos : 0 < m := by omega
    have hmlt : m < n := by omega
    have hmdiv : m ∣ n := ⟨2, by simpa [Nat.mul_comm] using hnm⟩
    have hmsupport : ∀ q : ℕ, q.Prime → q ∣ m → q = 2 := by
      intro q hq hqm
      exact hsupport q hq (dvd_trans hqm hmdiv)
    obtain ⟨k, hmk⟩ := ih m hmlt hmpos hmsupport
    refine ⟨k + 1, ?_⟩
    rw [hnm, hmk, pow_succ]
    ring

theorem odd_nat_eq_one_of_only_two_prime_divisors (n : ℕ) (hnodd : Odd n)
    (hsupport : ∀ p : ℕ, p.Prime → p ∣ n → p = 2) : n = 1 := by
  by_contra hnone
  obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd hnone
  have hp2 : p = 2 := hsupport p hp hpn
  have htwodiv : 2 ∣ n := by simpa [hp2] using hpn
  have hzero : n % 2 = 0 := Nat.mod_eq_zero_of_dvd htwodiv
  have hone : n % 2 = 1 := Nat.odd_iff.mp hnodd
  omega

theorem IsABCTriple.eq_one_one_two_of_only_two_prime_divisors
    {a b c : ℕ} (h : IsABCTriple a b c)
    (hsupport : ∀ p : ℕ, p.Prime → p ∣ a * b * c → p = 2) :
    a = 1 ∧ b = 1 ∧ c = 2 := by
  have hsupporta : ∀ p : ℕ, p.Prime → p ∣ a → p = 2 := by
    intro p hp hdiv
    exact hsupport p hp (dvd_trans hdiv ⟨b * c, by ring⟩)
  have hsupportb : ∀ p : ℕ, p.Prime → p ∣ b → p = 2 := by
    intro p hp hdiv
    exact hsupport p hp (dvd_trans hdiv ⟨a * c, by ring⟩)
  have hsupportc : ∀ p : ℕ, p.Prime → p ∣ c → p = 2 := by
    intro p hp hdiv
    exact hsupport p hp (dvd_trans hdiv ⟨a * b, by ring⟩)
  have hapos := h.1
  have hbpos := h.2.1
  have hsum := h.2.2.1
  have hamod : a % 2 = 0 ∨ a % 2 = 1 := by omega
  have hbmod : b % 2 = 0 ∨ b % 2 = 1 := by omega
  rcases hamod with ha | ha <;> rcases hbmod with hb | hb
  · have hcommon : 2 ∣ Nat.gcd a b := Nat.dvd_gcd
      (Nat.dvd_of_mod_eq_zero ha) (Nat.dvd_of_mod_eq_zero hb)
    rw [h.2.2.2.gcd_eq_one] at hcommon
    norm_num at hcommon
  · have hb1 : b = 1 := odd_nat_eq_one_of_only_two_prime_divisors b
      (Nat.odd_iff.mpr hb) hsupportb
    have hcmod : c % 2 = 1 := by
      rw [← hsum, Nat.add_mod, ha, hb]
    have hc1 : c = 1 := odd_nat_eq_one_of_only_two_prime_divisors c
      (Nat.odd_iff.mpr hcmod) hsupportc
    omega
  · have ha1 : a = 1 := odd_nat_eq_one_of_only_two_prime_divisors a
      (Nat.odd_iff.mpr ha) hsupporta
    have hcmod : c % 2 = 1 := by
      rw [← hsum, Nat.add_mod, ha, hb]
    have hc1 : c = 1 := odd_nat_eq_one_of_only_two_prime_divisors c
      (Nat.odd_iff.mpr hcmod) hsupportc
    omega
  · have ha1 : a = 1 := odd_nat_eq_one_of_only_two_prime_divisors a
      (Nat.odd_iff.mpr ha) hsupporta
    have hb1 : b = 1 := odd_nat_eq_one_of_only_two_prime_divisors b
      (Nat.odd_iff.mpr hb) hsupportb
    exact ⟨ha1, hb1, by omega⟩

theorem IsABCTriple.no_odd_prime_dvd_product_iff {a b c : ℕ}
    (h : IsABCTriple a b c) :
    (¬∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ a * b * c) ↔ (a, b, c) = (1, 1, 2) := by
  constructor
  · intro hnone
    have hsupport : ∀ p : ℕ, p.Prime → p ∣ a * b * c → p = 2 := by
      intro p hp hdiv
      by_contra hpne
      exact hnone ⟨p, hp, hpne, hdiv⟩
    rcases h.eq_one_one_two_of_only_two_prime_divisors hsupport with ⟨ha, hb, hc⟩
    simp [ha, hb, hc]
  · intro hequal
    have hequalities : a = 1 ∧ b = 1 ∧ c = 2 := by
      simpa only [Prod.mk.injEq] using hequal
    rcases hequalities with ⟨ha, hb, hc⟩
    rintro ⟨p, hp, hpne, hdiv⟩
    have hdivtwo : p ∣ 2 := by simpa [ha, hb, hc] using hdiv
    have hle : p ≤ 2 := Nat.le_of_dvd (by decide) hdivtwo
    have hge : 2 ≤ p := hp.two_le
    exact hpne (by omega)

theorem IsABCTriple.exists_odd_prime_dvd_product {a b c : ℕ}
    (h : IsABCTriple a b c) (hne : (a, b, c) ≠ (1, 1, 2)) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ a * b * c := by
  by_contra hnone
  exact hne (h.no_odd_prime_dvd_product_iff.mp hnone)

def abcOddBadPrimeSupport (a b c : ℕ) : Finset ℕ :=
  (a * b * c).primeFactors.filter (fun p => p ≠ 2)

theorem IsABCTriple.mem_abcOddBadPrimeSupport_iff {a b c p : ℕ}
    (h : IsABCTriple a b c) :
    p ∈ abcOddBadPrimeSupport a b c ↔ p.Prime ∧ p ≠ 2 ∧ p ∣ a * b * c := by
  have hproductne : a * b * c ≠ 0 := Nat.ne_of_gt h.abcInvariant_product_pos
  simp only [abcOddBadPrimeSupport, Finset.mem_filter, Nat.mem_primeFactors,
    hproductne, and_true]
  tauto

theorem IsABCTriple.abcOddBadPrimeSupport_nonempty_iff {a b c : ℕ}
    (h : IsABCTriple a b c) :
    (abcOddBadPrimeSupport a b c).Nonempty ↔ (a, b, c) ≠ (1, 1, 2) := by
  constructor
  · rintro ⟨p, hmem⟩ hequal
    have hnone := h.no_odd_prime_dvd_product_iff.mpr hequal
    exact hnone ⟨p, h.mem_abcOddBadPrimeSupport_iff.mp hmem⟩
  · intro hne
    obtain ⟨p, hp, hpne, hdiv⟩ := h.exists_odd_prime_dvd_product hne
    exact ⟨p, h.mem_abcOddBadPrimeSupport_iff.mpr ⟨hp, hpne, hdiv⟩⟩

theorem IsABCTriple.abcOddBadPrimeSupport_empty_iff {a b c : ℕ}
    (h : IsABCTriple a b c) :
    abcOddBadPrimeSupport a b c = ∅ ↔ (a, b, c) = (1, 1, 2) := by
  constructor
  · intro hempty
    by_contra hne
    obtain ⟨p, hp⟩ := h.abcOddBadPrimeSupport_nonempty_iff.mpr hne
    simpa [hempty] using hp
  · intro hequal
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    exact (h.abcOddBadPrimeSupport_nonempty_iff.mp ⟨p, hp⟩) hequal

theorem IsABCTriple.abcOddBadPrimeSupport_card_pos_iff {a b c : ℕ}
    (h : IsABCTriple a b c) :
    0 < (abcOddBadPrimeSupport a b c).card ↔ (a, b, c) ≠ (1, 1, 2) := by
  rw [Finset.card_pos, h.abcOddBadPrimeSupport_nonempty_iff]

theorem IsABCTriple.odd_bad_prime_mem_dvd_j_den {a b c p : ℕ}
    (h : IsABCTriple a b c) (hp : p ∈ abcOddBadPrimeSupport a b c) :
    p ∣ (abcJInvariant a b c).den := by
  rcases h.mem_abcOddBadPrimeSupport_iff.mp hp with ⟨hprime, hpne, hdiv⟩
  letI : Fact p.Prime := ⟨hprime⟩
  exact (h.prime_ne_two_dvd_abcJInvariant_den_iff hpne).mpr hdiv

theorem IsABCTriple.odd_bad_prime_mem_j_valuation_neg {a b c p : ℕ}
    (h : IsABCTriple a b c) (hp : p ∈ abcOddBadPrimeSupport a b c) :
    padicValRat p (abcJInvariant a b c) < 0 := by
  have hprime : p.Prime := (h.mem_abcOddBadPrimeSupport_iff.mp hp).1
  letI : Fact p.Prime := ⟨hprime⟩
  exact (rational_prime_dvd_den_iff_padicValRat_neg p (abcJInvariant a b c)).mp
    (h.odd_bad_prime_mem_dvd_j_den hp)

theorem IsABCTriple.exists_odd_prime_dvd_j_den_and_valuation_neg
    {a b c : ℕ} (h : IsABCTriple a b c) (hne : (a, b, c) ≠ (1, 1, 2)) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∈ abcOddBadPrimeSupport a b c ∧
      p ∣ (abcJInvariant a b c).den ∧ padicValRat p (abcJInvariant a b c) < 0 := by
  obtain ⟨p, hmem⟩ := h.abcOddBadPrimeSupport_nonempty_iff.mpr hne
  have hspec := h.mem_abcOddBadPrimeSupport_iff.mp hmem
  exact ⟨p, hspec.1, hspec.2.1, hmem, h.odd_bad_prime_mem_dvd_j_den hmem,
    h.odd_bad_prime_mem_j_valuation_neg hmem⟩

noncomputable def abcSelectedOddBadPrime {a b c : ℕ}
    (h : IsABCTriple a b c) (hne : (a, b, c) ≠ (1, 1, 2)) : ℕ :=
  Classical.choose (h.exists_odd_prime_dvd_product hne)

theorem abcSelectedOddBadPrime_spec {a b c : ℕ}
    (h : IsABCTriple a b c) (hne : (a, b, c) ≠ (1, 1, 2)) :
    (abcSelectedOddBadPrime h hne).Prime ∧ abcSelectedOddBadPrime h hne ≠ 2 ∧
      abcSelectedOddBadPrime h hne ∣ a * b * c := by
  exact Classical.choose_spec (h.exists_odd_prime_dvd_product hne)

theorem abcSelectedOddBadPrime_mem {a b c : ℕ}
    (h : IsABCTriple a b c) (hne : (a, b, c) ≠ (1, 1, 2)) :
    abcSelectedOddBadPrime h hne ∈ abcOddBadPrimeSupport a b c := by
  exact h.mem_abcOddBadPrimeSupport_iff.mpr (abcSelectedOddBadPrime_spec h hne)

theorem abcSelectedOddBadPrime_dvd_j_den {a b c : ℕ}
    (h : IsABCTriple a b c) (hne : (a, b, c) ≠ (1, 1, 2)) :
    abcSelectedOddBadPrime h hne ∣ (abcJInvariant a b c).den := by
  exact h.odd_bad_prime_mem_dvd_j_den (abcSelectedOddBadPrime_mem h hne)

theorem abcSelectedOddBadPrime_j_valuation_neg {a b c : ℕ}
    (h : IsABCTriple a b c) (hne : (a, b, c) ≠ (1, 1, 2)) :
    padicValRat (abcSelectedOddBadPrime h hne) (abcJInvariant a b c) < 0 := by
  exact h.odd_bad_prime_mem_j_valuation_neg (abcSelectedOddBadPrime_mem h hne)

theorem abcSelectedOddBadPrime_j_valuation_formula {a b c : ℕ}
    (h : IsABCTriple a b c) (hne : (a, b, c) ≠ (1, 1, 2)) :
    padicValRat (abcSelectedOddBadPrime h hne) (abcJInvariant a b c) =
      -2 * ((padicValNat (abcSelectedOddBadPrime h hne) a : ℤ) +
        (padicValNat (abcSelectedOddBadPrime h hne) b : ℤ) +
        (padicValNat (abcSelectedOddBadPrime h hne) c : ℤ)) := by
  have hspec := abcSelectedOddBadPrime_spec h hne
  letI : Fact (abcSelectedOddBadPrime h hne).Prime := ⟨hspec.1⟩
  exact h.abcJInvariant_padicValRat_of_prime_ne_two_dvd_product_sum
    hspec.2.1 hspec.2.2

theorem abcJInvariant_one_one_two : abcJInvariant 1 1 2 = 1728 := by
  norm_num [abcJInvariant, abcInvariantNumerator, abcInvariantDenominator,
    abcInvariantPolynomial]

theorem IsABCTriple.abcJInvariant_den_ne_one_of_nonexceptional
    {a b c : ℕ} (h : IsABCTriple a b c) (hne : (a, b, c) ≠ (1, 1, 2)) :
    (abcJInvariant a b c).den ≠ 1 := by
  intro hdenone
  obtain ⟨p, hp, _, _, hpden, _⟩ := h.exists_odd_prime_dvd_j_den_and_valuation_neg hne
  rw [hdenone] at hpden
  exact hp.ne_one (Nat.eq_one_of_dvd_one hpden)

theorem IsABCTriple.abcJInvariant_ne_intCast_of_nonexceptional
    {a b c : ℕ} (h : IsABCTriple a b c) (hne : (a, b, c) ≠ (1, 1, 2))
    (z : ℤ) : abcJInvariant a b c ≠ (z : ℚ) := by
  intro hequal
  apply h.abcJInvariant_den_ne_one_of_nonexceptional hne
  rw [hequal]
  exact Rat.den_intCast z

theorem IsABCTriple.abcJInvariant_not_integer_of_nonexceptional
    {a b c : ℕ} (h : IsABCTriple a b c) (hne : (a, b, c) ≠ (1, 1, 2)) :
    ¬∃ z : ℤ, abcJInvariant a b c = (z : ℚ) := by
  rintro ⟨z, hequal⟩
  exact h.abcJInvariant_ne_intCast_of_nonexceptional hne z hequal

theorem IsABCTriple.abcJInvariant_integer_iff_exceptional {a b c : ℕ}
    (h : IsABCTriple a b c) :
    (∃ z : ℤ, abcJInvariant a b c = (z : ℚ)) ↔ (a, b, c) = (1, 1, 2) := by
  constructor
  · intro hinteger
    by_contra hne
    exact h.abcJInvariant_not_integer_of_nonexceptional hne hinteger
  · intro hequal
    have hequalities : a = 1 ∧ b = 1 ∧ c = 2 := by
      simpa only [Prod.mk.injEq] using hequal
    rcases hequalities with ⟨ha, hb, hc⟩
    refine ⟨1728, ?_⟩
    simpa [ha, hb, hc] using abcJInvariant_one_one_two

theorem abcLogarithmicRadicalBound_iff_nonexceptional (slope : ℝ) :
    (∃ constant : ℝ, ∀ a b c : ℕ, IsABCTriple a b c →
      Real.log (c : ℝ) ≤ slope * Real.log (radical (a * b * c) : ℝ) + constant) ↔
    (∃ constant : ℝ, ∀ a b c : ℕ, IsABCTriple a b c →
      (a, b, c) ≠ (1, 1, 2) →
      Real.log (c : ℝ) ≤ slope * Real.log (radical (a * b * c) : ℝ) + constant) := by
  constructor
  · rintro ⟨constant, hbound⟩
    exact ⟨constant, fun a b c h _ => hbound a b c h⟩
  · rintro ⟨constant, hbound⟩
    let exceptionalError : ℝ := Real.log 2 - slope * Real.log (radical 2 : ℝ)
    refine ⟨max constant exceptionalError, ?_⟩
    intro a b c h
    by_cases hequal : (a, b, c) = (1, 1, 2)
    · have hequalities : a = 1 ∧ b = 1 ∧ c = 2 := by
        simpa only [Prod.mk.injEq] using hequal
      rcases hequalities with ⟨ha, hb, hc⟩
      subst a
      subst b
      subst c
      have hexception := le_max_right constant exceptionalError
      dsimp [exceptionalError] at hexception
      norm_num only [Nat.one_mul, Nat.cast_ofNat] at *
      linarith
    · have hregular := hbound a b c h hequal
      have hconstant := le_max_left constant exceptionalError
      linarith

theorem abcPositiveLogarithmicRadicalBound_iff_nonexceptional (slope : ℝ) :
    (∃ constant : ℝ, 0 < constant ∧ ∀ a b c : ℕ, IsABCTriple a b c →
      Real.log (c : ℝ) ≤ slope * Real.log (radical (a * b * c) : ℝ) + constant) ↔
    (∃ constant : ℝ, 0 < constant ∧ ∀ a b c : ℕ, IsABCTriple a b c →
      (a, b, c) ≠ (1, 1, 2) →
      Real.log (c : ℝ) ≤ slope * Real.log (radical (a * b * c) : ℝ) + constant) := by
  constructor
  · rintro ⟨constant, hpositive, hbound⟩
    exact ⟨constant, hpositive, fun a b c h _ => hbound a b c h⟩
  · rintro ⟨constant, hpositive, hbound⟩
    obtain ⟨enlargedConstant, henlargedBound⟩ :=
      (abcLogarithmicRadicalBound_iff_nonexceptional slope).mpr ⟨constant, hbound⟩
    refine ⟨max constant enlargedConstant,
      lt_of_lt_of_le hpositive (le_max_left _ _), ?_⟩
    intro a b c h
    have hregular := henlargedBound a b c h
    have henlarged := le_max_right constant enlargedConstant
    linarith

theorem abcMultiplicativeRadicalBound_iff_nonexceptional (exponent : ℝ) :
    (∃ constant : ℝ, 0 < constant ∧ ∀ a b c : ℕ, IsABCTriple a b c →
      (c : ℝ) ≤ constant * (radical (a * b * c) : ℝ) ^ exponent) ↔
    (∃ constant : ℝ, 0 < constant ∧ ∀ a b c : ℕ, IsABCTriple a b c →
      (a, b, c) ≠ (1, 1, 2) →
      (c : ℝ) ≤ constant * (radical (a * b * c) : ℝ) ^ exponent) := by
  constructor
  · rintro ⟨constant, hpositive, hbound⟩
    exact ⟨constant, hpositive, fun a b c h _ => hbound a b c h⟩
  · rintro ⟨constant, hpositive, hbound⟩
    let exceptionalScale : ℝ := (radical 2 : ℝ) ^ exponent
    have hscalepos : 0 < exceptionalScale := by
      apply Real.rpow_pos_of_pos
      exact_mod_cast natRadical_pos 2
    refine ⟨max constant (2 / exceptionalScale),
      lt_of_lt_of_le hpositive (le_max_left _ _), ?_⟩
    intro a b c h
    by_cases hequal : (a, b, c) = (1, 1, 2)
    · have hequalities : a = 1 ∧ b = 1 ∧ c = 2 := by
        simpa only [Prod.mk.injEq] using hequal
      rcases hequalities with ⟨ha, hb, hc⟩
      subst a
      subst b
      subst c
      have hratio := le_max_right constant (2 / exceptionalScale)
      have hscaled := mul_le_mul_of_nonneg_right hratio (le_of_lt hscalepos)
      have hcancel : (2 / exceptionalScale) * exceptionalScale = 2 := by
        exact div_mul_cancel₀ 2 (ne_of_gt hscalepos)
      rw [hcancel] at hscaled
      simpa only [Nat.one_mul, Nat.cast_ofNat, exceptionalScale] using hscaled
    · have hscale : 0 ≤ (radical (a * b * c) : ℝ) ^ exponent := by
        apply le_of_lt
        apply Real.rpow_pos_of_pos
        exact_mod_cast natRadical_pos (a * b * c)
      exact le_trans (hbound a b c h hequal)
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hscale)

theorem abcMultiplicativeRadicalFamily_iff_nonexceptional :
    (∀ epsilon : ℝ, 0 < epsilon → ∃ constant : ℝ, 0 < constant ∧
      ∀ a b c : ℕ, IsABCTriple a b c →
        (c : ℝ) ≤ constant * (radical (a * b * c) : ℝ) ^ (1 + epsilon)) ↔
    (∀ epsilon : ℝ, 0 < epsilon → ∃ constant : ℝ, 0 < constant ∧
      ∀ a b c : ℕ, IsABCTriple a b c → (a, b, c) ≠ (1, 1, 2) →
        (c : ℝ) ≤ constant * (radical (a * b * c) : ℝ) ^ (1 + epsilon)) := by
  constructor
  · intro hbound epsilon hepsilon
    exact (abcMultiplicativeRadicalBound_iff_nonexceptional (1 + epsilon)).mp
      (hbound epsilon hepsilon)
  · intro hbound epsilon hepsilon
    exact (abcMultiplicativeRadicalBound_iff_nonexceptional (1 + epsilon)).mpr
      (hbound epsilon hepsilon)

end LeanFormal.IUT
