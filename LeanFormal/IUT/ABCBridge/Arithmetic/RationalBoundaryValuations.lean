/-
  Boundary `p`-adic valuation facts for a rational number `x`.

  Mathlib's `padicValRat p` is the actual valuation on `ℚ` (totalized to `0` when the
  argument is `0` or `p = 1`).  Here we express it at the two finite boundary components
  `0` and `1` of the rational point through the three intrinsic integer coordinates

    `x.num.natAbs`, `((x.den : ℤ) - x.num).natAbs`, `x.den`,

  and record the sign alternatives for the pair `(padicValRat p x, padicValRat p (1 - x))`.

  This is arithmetic valuation data only.  It does not identify a geometric conductor and
  does not prove the IUT IV Cor. 2.3 estimate.
-/
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPrimeSupport
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

namespace LeanFormal.IUT

/-! ## Coordinates of the second boundary component `1 - x` -/

/-- `1 - x` as the `Rat.divInt` of the intrinsic pair `(x.den - x.num, x.den)`. -/
theorem one_sub_eq_divInt_num_den (x : ℚ) :
    (1 : ℚ) - x = Rat.divInt ((x.den : ℤ) - x.num) (x.den : ℤ) := by
  rw [sub_eq_add_neg, Rat.add_num_den, Rat.num_one, Rat.den_one, Rat.neg_num, Rat.neg_den]
  congr 1 <;> ring

/-! ## Valuation coordinates via numerator and denominator -/

/-- `padicValRat` in terms of the numerator and denominator of the reduced fraction. -/
theorem padicValRat_eq_natAbs_sub_den (p : ℕ) (x : ℚ) :
    padicValRat p x =
      (padicValNat p x.num.natAbs : ℤ) - (padicValNat p x.den : ℤ) :=
  rfl

/-- `padicValRat p (1 - x)` in terms of the boundary gap `(x.den : ℤ) - x.num` and `x.den`
(or `0` when the library totalizes the valuation). -/
theorem padicValRat_one_sub_eq_natAbs_sub_den {p : ℕ} (hp : Nat.Prime p) {x : ℚ}
    (hx1 : x ≠ 1) :
    padicValRat p (1 - x) =
      (padicValNat p (((x.den : ℤ) - x.num).natAbs) : ℤ) - (padicValNat p x.den : ℤ) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hq : (1 : ℚ) - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx1)
  have hd : (x.den : ℤ) ≠ 0 := by exact_mod_cast Rat.den_nz x
  have hgap : (x.den : ℤ) - x.num ≠ 0 := by
    intro h0
    apply hq
    rw [one_sub_eq_divInt_num_den x, h0, Rat.zero_divInt]
  have hdef := padicValRat.defn p hq (one_sub_eq_divInt_num_den x)
  rw [hdef, ← padicValInt.of_ne_one_ne_zero hp.ne_one hgap,
    ← padicValInt.of_ne_one_ne_zero hp.ne_one hd]
  simp only [padicValInt, Int.natAbs_natCast]

/-! ## Sign alternatives at the two finite boundary components -/

/-- The two boundary valuations cannot be an arbitrary pair: for `x ≠ 0, 1` and prime `p`
only four sign configurations occur. -/
theorem padicValRat_boundary_sign_pattern {p : ℕ} (hp : Nat.Prime p) {x : ℚ}
    (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    (padicValRat p x = 0 ∧ padicValRat p (1 - x) = 0) ∨
    (0 < padicValRat p x ∧ padicValRat p (1 - x) = 0) ∨
    (padicValRat p x = 0 ∧ 0 < padicValRat p (1 - x)) ∨
    (padicValRat p x < 0 ∧ padicValRat p (1 - x) = padicValRat p x) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hx1' : (1 : ℚ) - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx1)
  have hxsum : x + (1 - x) = 1 := by ring
  have hsum : x + (1 - x) ≠ 0 := by rw [hxsum]; exact one_ne_zero
  have hmin : min (padicValRat p x) (padicValRat p (1 - x)) ≤ 0 := by
    have h := padicValRat.min_le_padicValRat_add (p := p) hsum
    rwa [hxsum, padicValRat.one] at h
  by_cases heq : padicValRat p x = padicValRat p (1 - x)
  · have hle : padicValRat p x ≤ 0 := by
      have h := hmin
      rw [← heq, min_self] at h
      exact h
    rcases lt_or_eq_of_le hle with hlt | h0
    · exact Or.inr (Or.inr (Or.inr ⟨hlt, heq.symm⟩))
    · exact Or.inl ⟨h0, by rw [← heq]; exact h0⟩
  · have hadd : (0 : ℤ) = min (padicValRat p x) (padicValRat p (1 - x)) := by
      have h := padicValRat.add_eq_min (p := p) hsum hx0 hx1' heq
      rw [hxsum, padicValRat.one] at h
      exact h
    have hone : padicValRat p x = 0 ∨ padicValRat p (1 - x) = 0 := by
      rcases le_total (padicValRat p x) (padicValRat p (1 - x)) with h | h
      · left
        have h' : min (padicValRat p x) (padicValRat p (1 - x)) = padicValRat p x :=
          min_eq_left h
        rw [h'] at hadd
        exact hadd.symm
      · right
        have h' : min (padicValRat p x) (padicValRat p (1 - x)) = padicValRat p (1 - x) :=
          min_eq_right h
        rw [h'] at hadd
        exact hadd.symm
    have hxge : 0 ≤ padicValRat p x := by
      rw [hadd]; exact min_le_left _ _
    have hwge : 0 ≤ padicValRat p (1 - x) := by
      rw [hadd]; exact min_le_right _ _
    rcases hone with hx0' | hw0
    · rcases lt_or_eq_of_le hwge with hwpos | hw0'
      · exact Or.inr (Or.inr (Or.inl ⟨hx0', hwpos⟩))
      · exact Or.inl ⟨hx0', hw0'.symm⟩
    · rcases lt_or_eq_of_le hxge with hxpos | hx0''
      · exact Or.inr (Or.inl ⟨hxpos, hw0⟩)
      · exact Or.inl ⟨hx0''.symm, hw0⟩

/-! ## Divisibility on the boundary coordinates -/

/-- A prime cannot divide two coprime natural numbers. -/
theorem not_coprime_of_prime_dvd_both {p a b : ℕ} (hp : Nat.Prime p) (hcop : a.Coprime b)
    (ha : p ∣ a) (hb : p ∣ b) : False := by
  have hg : p ∣ a.gcd b := Nat.dvd_gcd ha hb
  rw [hcop.gcd_eq_one] at hg
  exact hp.ne_one (Nat.dvd_one.mp hg)

/-- The boundary gap `(x.den : ℤ) - x.num` and the denominator `x.den` are coprime. -/
theorem coprime_den_sub_num_den (x : ℚ) :
    Nat.Coprime (((x.den : ℤ) - x.num).natAbs) x.den := by
  have hcop : IsCoprime x.num (x.den : ℤ) := by
    rw [Int.isCoprime_iff_nat_coprime]
    simpa using Rat.reduced x
  have hcop' : IsCoprime ((x.den : ℤ) - x.num) (x.den : ℤ) := by
    have h := hcop.neg_left
    have h2 : IsCoprime (-x.num + 1 * (x.den : ℤ)) (x.den : ℤ) := h.add_mul_right_left 1
    have heq : -x.num + 1 * (x.den : ℤ) = (x.den : ℤ) - x.num := by ring
    rwa [heq] at h2
  simpa using (Int.isCoprime_iff_nat_coprime.mp hcop')

/-- For `x ≠ 0` and prime `p`, `padicValRat p x` is nonzero exactly when `p` divides one of
the two denominator-side coordinates of `x`. -/
theorem padicValRat_ne_zero_iff_dvd_num_or_den {p : ℕ} (hp : Nat.Prime p) {x : ℚ}
    (hx : x ≠ 0) :
    padicValRat p x ≠ 0 ↔ p ∣ x.num.natAbs ∨ p ∣ x.den := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hnum : x.num.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr hx)
  have hden : x.den ≠ 0 := Rat.den_nz x
  have hcoord := padicValRat_eq_natAbs_sub_den p x
  constructor
  · intro h
    have hne : (padicValNat p x.num.natAbs : ℤ) ≠ (padicValNat p x.den : ℤ) := by
      rw [hcoord] at h
      exact sub_ne_zero.mp h
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · right
      exact (dvd_iff_padicValNat_ne_zero hden).mpr (by omega)
    · left
      exact (dvd_iff_padicValNat_ne_zero hnum).mpr (by omega)
  · rintro (h | h)
    · intro hzero
      have hnum0 : padicValNat p x.num.natAbs ≠ 0 := (dvd_iff_padicValNat_ne_zero hnum).mp h
      have heq : (padicValNat p x.num.natAbs : ℤ) = (padicValNat p x.den : ℤ) := by
        rw [hcoord] at hzero
        exact sub_eq_zero.mp hzero
      have hden0 : padicValNat p x.den ≠ 0 := by omega
      exact not_coprime_of_prime_dvd_both hp (Rat.reduced x) h
        ((dvd_iff_padicValNat_ne_zero hden).mpr hden0)
    · intro hzero
      have hden0 : padicValNat p x.den ≠ 0 := (dvd_iff_padicValNat_ne_zero hden).mp h
      have heq : (padicValNat p x.num.natAbs : ℤ) = (padicValNat p x.den : ℤ) := by
        rw [hcoord] at hzero
        exact sub_eq_zero.mp hzero
      have hnum0 : padicValNat p x.num.natAbs ≠ 0 := by omega
      exact not_coprime_of_prime_dvd_both hp (Rat.reduced x)
        ((dvd_iff_padicValNat_ne_zero hnum).mpr hnum0) h

/-- For `x ≠ 1` and prime `p`, `padicValRat p (1 - x)` is nonzero exactly when `p` divides
one of the two denominator-side coordinates of `1 - x`. -/
theorem padicValRat_one_sub_ne_zero_iff_dvd_gap_or_den {p : ℕ} (hp : Nat.Prime p) {x : ℚ}
    (hx1 : x ≠ 1) :
    padicValRat p (1 - x) ≠ 0 ↔ p ∣ ((x.den : ℤ) - x.num).natAbs ∨ p ∣ x.den := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hgap0 : (x.den : ℤ) - x.num ≠ 0 := by
    intro h0
    apply (sub_ne_zero.mpr (Ne.symm hx1) : (1 : ℚ) - x ≠ 0)
    rw [one_sub_eq_divInt_num_den x, h0, Rat.zero_divInt]
  have hgap : ((x.den : ℤ) - x.num).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hgap0
  have hden : x.den ≠ 0 := Rat.den_nz x
  have hcoord := padicValRat_one_sub_eq_natAbs_sub_den hp hx1
  constructor
  · intro h
    have hne : (padicValNat p (((x.den : ℤ) - x.num).natAbs) : ℤ) ≠
        (padicValNat p x.den : ℤ) := by
      rw [hcoord] at h
      exact sub_ne_zero.mp h
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · right
      exact (dvd_iff_padicValNat_ne_zero hden).mpr (by omega)
    · left
      exact (dvd_iff_padicValNat_ne_zero hgap).mpr (by omega)
  · rintro (h | h)
    · intro hzero
      have hgapnz : padicValNat p (((x.den : ℤ) - x.num).natAbs) ≠ 0 :=
        (dvd_iff_padicValNat_ne_zero hgap).mp h
      have heq : (padicValNat p (((x.den : ℤ) - x.num).natAbs) : ℤ) =
          (padicValNat p x.den : ℤ) := by
        rw [hcoord] at hzero
        exact sub_eq_zero.mp hzero
      have hden0 : padicValNat p x.den ≠ 0 := by omega
      exact not_coprime_of_prime_dvd_both hp (coprime_den_sub_num_den x) h
        ((dvd_iff_padicValNat_ne_zero hden).mpr hden0)
    · intro hzero
      have hden0 : padicValNat p x.den ≠ 0 := (dvd_iff_padicValNat_ne_zero hden).mp h
      have heq : (padicValNat p (((x.den : ℤ) - x.num).natAbs) : ℤ) =
          (padicValNat p x.den : ℤ) := by
        rw [hcoord] at hzero
        exact sub_eq_zero.mp hzero
      have hgapnz : padicValNat p (((x.den : ℤ) - x.num).natAbs) ≠ 0 := by omega
      exact not_coprime_of_prime_dvd_both hp (coprime_den_sub_num_den x)
        ((dvd_iff_padicValNat_ne_zero hgap).mpr hgapnz) h

end LeanFormal.IUT
