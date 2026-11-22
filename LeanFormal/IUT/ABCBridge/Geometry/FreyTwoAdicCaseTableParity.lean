import LeanFormal.IUT.ABCBridge.Geometry.FreyTwoAdicCaseTableCards
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Parity and 2-adic valuation slots for the `p = 2` abc-Frey case table

This file advances the shape slots of `FreyTwoAdicCaseTableCards` into
concrete, proved propositions.  The frozen card file is not modified.

* `AbcFreyTripleShape.exactlyOneCoordinateEven`: every inhabited abc-Frey
  triple shape (sum, pairwise coprimality and non-vanishing as slots) has
  exactly one even coordinate; this proves the statement shape
  `ExactlyOneCoordinateEvenShape` of the card file.
* `padicValNat_two_eq_one_iff`: for `n ≠ 0`, `padicValNat 2 n = 1` exactly
  when `n % 4 = 2`.
* `odd_add_mod_four_eq_two_iff` and `padicValNat_two_odd_add_eq_one_iff`:
  for odd `a`, `b`, the valuation `v₂(a + b)` equals `1` exactly when
  `a % 4 = b % 4`; this is the entry criterion `γ = 1` versus `γ ≥ 2` for
  the case C row (both coordinates odd) of the `p = 2` case table.

These are arithmetic facts only: no conductor exponent, Ogg–Saito constant,
or literature value is stated or used here.
-/

namespace LeanFormal.IUT

/-- For `n ≠ 0`, the `2`-adic valuation is `1` exactly when `n % 4 = 2`. -/
theorem padicValNat_two_eq_one_iff (n : ℕ) (hn : n ≠ 0) :
    padicValNat 2 n = 1 ↔ n % 4 = 2 := by
  have h1 : 1 ≤ padicValNat 2 n ↔ 2 ∣ n := by
    rw [← padicValNat_dvd_iff_le (p := 2) (a := n) (n := 1) hn]
    norm_num
  have h2 : 2 ≤ padicValNat 2 n ↔ 4 ∣ n := by
    rw [← padicValNat_dvd_iff_le (p := 2) (a := n) (n := 2) hn]
    norm_num
  have hv : padicValNat 2 n = 1 ↔ 1 ≤ padicValNat 2 n ∧ ¬ 2 ≤ padicValNat 2 n := by
    constructor
    · intro h
      constructor <;> omega
    · rintro ⟨h1', h2'⟩
      omega
  rw [hv, h1, h2]
  constructor
  · rintro ⟨hd2, hd4⟩
    have hm2 : n % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp hd2
    have hm4 : n % 4 ≠ 0 := fun h0 => hd4 (Nat.dvd_iff_mod_eq_zero.mpr h0)
    have hchain : n % 4 % 2 = 0 := by
      rw [Nat.mod_mod_of_dvd n (by norm_num : (2 : ℕ) ∣ 4)]
      exact hm2
    have hlt : n % 4 < 4 := Nat.mod_lt n (by norm_num)
    interval_cases hcase : n % 4 <;> simp_all
  · intro h
    constructor
    · rw [Nat.dvd_iff_mod_eq_zero]
      rw [← Nat.mod_mod_of_dvd n (by norm_num : (2 : ℕ) ∣ 4), h]
    · intro hd4
      have h0 : n % 4 = 0 := Nat.dvd_iff_mod_eq_zero.mp hd4
      omega

/-- For odd `a` and `b`, the sum is `2` modulo `4` exactly when `a` and `b`
are congruent modulo `4`. -/
theorem odd_add_mod_four_eq_two_iff {a b : ℕ} (ha : Odd a) (hb : Odd b) :
    (a + b) % 4 = 2 ↔ a % 4 = b % 4 := by
  obtain ⟨i, hi⟩ := ha
  obtain ⟨j, hj⟩ := hb
  rw [hi, hj]
  rcases Nat.even_or_odd i with ⟨k, hk⟩ | ⟨k, hk⟩ <;>
    rcases Nat.even_or_odd j with ⟨l, hl⟩ | ⟨l, hl⟩ <;>
    (constructor <;> intro h <;> omega)

/-- For odd `a` and `b`, the `2`-adic valuation of the sum is `1` exactly
when `a` and `b` are congruent modulo `4`. -/
theorem padicValNat_two_odd_add_eq_one_iff {a b : ℕ} (ha : Odd a) (hb : Odd b) :
    padicValNat 2 (a + b) = 1 ↔ a % 4 = b % 4 := by
  have hne : a + b ≠ 0 := by
    obtain ⟨i, hi⟩ := ha
    omega
  rw [padicValNat_two_eq_one_iff (a + b) hne]
  exact odd_add_mod_four_eq_two_iff ha hb

end LeanFormal.IUT

namespace LeanFormal.IUT.ABCBridge.Geometry.FreyTwoAdicCaseTableCards

/-- The parity slot of the `p = 2` case table, proved: every inhabited
abc-Frey triple shape has exactly one even coordinate. -/
theorem AbcFreyTripleShape.exactlyOneCoordinateEven (t : AbcFreyTripleShape) :
    ExactlyOneCoordinateEvenShape t := by
  have hcop : Nat.gcd t.a t.b = 1 := t.pairwiseCoprimeSlot.1
  have hnot : ¬ (2 ∣ t.a ∧ 2 ∣ t.b) := by
    rintro ⟨ha, hb⟩
    have h2 : 2 ∣ Nat.gcd t.a t.b := Nat.dvd_gcd ha hb
    rw [hcop] at h2
    obtain ⟨k, hk⟩ := h2
    omega
  have hsum : t.c = t.a + t.b := t.sumSlot
  have ha2 : t.a % 2 < 2 := Nat.mod_lt t.a (by norm_num)
  have hb2 : t.b % 2 < 2 := Nat.mod_lt t.b (by norm_num)
  have haC : t.a % 2 = 0 ∨ t.a % 2 = 1 := by omega
  have hbC : t.b % 2 = 0 ∨ t.b % 2 = 1 := by omega
  rcases haC with ha0 | ha1 <;> rcases hbC with hb0 | hb1
  · exact absurd ⟨Nat.dvd_iff_mod_eq_zero.mpr ha0, Nat.dvd_iff_mod_eq_zero.mpr hb0⟩ hnot
  · exact Or.inl ⟨Nat.even_iff.mpr ha0, Nat.odd_iff.mpr hb1, Nat.odd_iff.mpr (by omega)⟩
  · exact Or.inr (Or.inl ⟨Nat.odd_iff.mpr ha1, Nat.even_iff.mpr hb0, Nat.odd_iff.mpr (by omega)⟩)
  · exact Or.inr (Or.inr ⟨Nat.odd_iff.mpr ha1, Nat.odd_iff.mpr hb1, Nat.even_iff.mpr (by omega)⟩)

end LeanFormal.IUT.ABCBridge.Geometry.FreyTwoAdicCaseTableCards
