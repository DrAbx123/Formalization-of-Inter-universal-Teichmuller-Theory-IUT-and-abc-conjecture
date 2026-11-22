import LeanFormal.IUT.ABCBridge.Statement
import LeanFormal.IUT.ABCBridge.Arithmetic.PrimitiveTriple
import Mathlib.NumberTheory.Height.NumberField

/-!
# Rational point dictionary for primitive additive (ABC) triples

This file is the arithmetic dictionary component beneath the integer ABC statement of
`LeanFormal.IUT.ABCBridge.Statement`.  Nothing here is an IUT theorem, a comparison, a GenEll
conductor, or a proof of ABC; it records only the elementary arithmetic of the rational point
`x = a / c` attached to an actual `IsABCTriple`.

## Semantics actually bound

`LeanFormal.IUT.IsABCTriple` is `abbrev IsABCTriple := PrimitiveAdditiveTriple`, and the imported
`LeanFormal.IUT.PrimitiveAdditiveTriple : Nat → Nat → Nat → Prop` is a plain `def` (it has no
`mk`), definitionally the four-field conjunction

`0 < a ∧ 0 < b ∧ a + b = c ∧ Nat.Coprime a b`.

`isABCTriple_iff_positivePrimitiveAdditiveTriple` proves this equivalence componentwise in both
directions.  In particular the predicate has no extra degeneracy: `a` and `b` are strictly
positive, `c` is their sum, and `a`, `b` are coprime.  No hypothesis has been strengthened or
weakened relative to the imported predicate.

## Results

For `a b c : Nat` with `h : IsABCTriple a b c`, write `x = abcRationalPoint a c`, so that
`x = (a : Rat) / (c : Rat)`:

* `abcRationalPoint_ne_zero`, `abcRationalPoint_ne_one`: `x ≠ 0` and `x ≠ 1`, so `x` lies in the
  complement of `{0, 1}` in the multiplicative group `Ratˣ ∪ {0}`.
* `abcRationalPoint_num`, `abcRationalPoint_den`: the genuine Mathlib reduced coordinates satisfy
  `x.num = (a : Int)` and `x.den = c`; `abcRationalPoint_num_natAbs` and
  `abcRationalPoint_reduced` record the reduced/gcd consequences, and
  `abcRationalPoint_coordinate_coprime` recovers `Nat.Coprime a c` from them.
* `abcRationalPoint_den_sub_num`: `(x.den : Int) - x.num = (b : Int)`, the third `{0, 1, ∞}`
  coordinate.
* `abcRationalPoint_mulHeight₁`: the canonical Mathlib multiplicative height
  `Height.mulHeight₁ x` equals `c`.
* `abcRationalPoint_logHeight₁`: the canonical Mathlib logarithmic height
  `Height.logHeight₁ x` equals `Real.log c`.
* `prime_dvd_abc_iff_prime_dvd_point_coordinates`: for every `p : Nat` with `hp : p.Prime`,
  `p ∣ a * b * c ↔ p ∣ x.num.natAbs ∨ p ∣ ((x.den : Int) - x.num).natAbs ∨ p ∣ x.den`.
  The three right-hand disjuncts are exactly the finite prime supports of the three
  `{0, 1, ∞}`-coordinates `a`, `b`, `c` read through `x`; this is the finite-prime-support
  dictionary, and no conductor object is introduced to state it.
* `prime_dvd_radical_abc_iff`: the radical factorization `radical (a * b * c) =
  radical a * radical b * radical c` of `IsABCTriple.radical_product_eq` distributes prime
  divisibility to the three factors.

## Consumer interface and remaining boundaries

A future `P1 minus {0, 1, ∞}` specialization can consume the following public facts, each of
which is proved here about the *actual* imported predicate and the *actual* canonical Mathlib
height:

* membership of the point in `P1 \ {0, 1, ∞}`: `abcRationalPoint_ne_zero`,
  `abcRationalPoint_ne_one`;
* normalized coordinates and their coprimality: `abcRationalPoint_num`,
  `abcRationalPoint_den`, `abcRationalPoint_reduced`, `abcRationalPoint_coordinate_coprime`;
* the third coordinate: `abcRationalPoint_den_sub_num`;
* the two standard heights: `abcRationalPoint_mulHeight₁`, `abcRationalPoint_logHeight₁`;
* the finite prime support identity: `prime_dvd_abc_iff_prime_dvd_point_coordinates`, with
  `prime_dvd_radical_abc_iff` as the radical-facing form.

Still *not* established here, and deliberately left outside this file: no GenEll conductor
equivalence, no conductor or height is introduced by definition merely to make an identity
hold, no IUT III/IV hull, comparison, or geometric normalization is instantiated, and no ABC
inequality or full ABC statement is proved.  In particular the finite prime support above is
the arithmetic support identity itself; it is not asserted to equal any conductor of a
GenEll object.
-/

namespace LeanFormal.IUT

/-! ### 1. The exact semantics of `IsABCTriple` -/

/-- The positive primitive additive predicate, spelled out literally: `a` and `b` are strictly
positive, `c` is their sum, and `a` and `b` are coprime. -/
def PositivePrimitiveAdditiveTriple (a b c : Nat) : Prop :=
  0 < a ∧ 0 < b ∧ a + b = c ∧ Nat.Coprime a b

/-- `IsABCTriple` is exactly the positive primitive additive predicate.  Both directions are
proved componentwise, so this is an equivalence of the actual predicates, not a restatement. -/
theorem isABCTriple_iff_positivePrimitiveAdditiveTriple (a b c : Nat) :
    IsABCTriple a b c ↔ PositivePrimitiveAdditiveTriple a b c := by
  constructor
  · rintro ⟨ha, hb, hs, hc⟩
    exact ⟨ha, hb, hs, hc⟩
  · rintro ⟨ha, hb, hs, hc⟩
    exact ⟨ha, hb, hs, hc⟩

/-! ### 2. The rational point `x = a / c` -/

/-- The rational point `a / c` attached to the pair `(a, c)`. -/
def abcRationalPoint (a c : Nat) : Rat := (a : Rat) / (c : Rat)

theorem abcRationalPoint_eq_div (a c : Nat) :
    abcRationalPoint a c = (a : Rat) / (c : Rat) := rfl

/-! ### 3. Reduced coordinates -/

/-- The numerator of `(a : Rat) / (c : Rat)` for a nonzero denominator `c` coprime to `a`. -/
theorem ratDivNatCast_num {a c : Nat} (hc : c ≠ 0) (h : Nat.Coprime a c) :
    ((a : Rat) / (c : Rat)).num = (a : Int) := by
  have hx : ((a : Rat) / (c : Rat)) = Rat.divInt (a : Int) (c : Int) := by
    rw [Rat.divInt_eq_div]
    push_cast
    ring
  have hgcd : Int.gcd (c : Int) (a : Int) = 1 := by
    rw [Int.gcd_natCast_natCast, Nat.gcd_comm]
    exact h.gcd_eq_one
  rw [hx, Rat.num_divInt,
    Int.sign_eq_one_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hc)), hgcd]
  simp

/-- The denominator of `(a : Rat) / (c : Rat)` for a nonzero denominator `c` coprime to `a`. -/
theorem ratDivNatCast_den {a c : Nat} (hc : c ≠ 0) (h : Nat.Coprime a c) :
    ((a : Rat) / (c : Rat)).den = c := by
  have hx : ((a : Rat) / (c : Rat)) = Rat.divInt (a : Int) (c : Int) := by
    rw [Rat.divInt_eq_div]
    push_cast
    ring
  have hgcd : Int.gcd (c : Int) (a : Int) = 1 := by
    rw [Int.gcd_natCast_natCast, Nat.gcd_comm]
    exact h.gcd_eq_one
  rw [hx, Rat.den_divInt, if_neg (by exact_mod_cast hc : (c : Int) ≠ 0), hgcd,
    Int.natAbs_natCast]
  simp

/-- The reduced numerator of the point is the original numerator. -/
theorem abcRationalPoint_num {a b c : Nat} (h : IsABCTriple a b c) :
    (abcRationalPoint a c).num = (a : Int) := by
  have ha : 0 < a := h.1
  have hs : a + b = c := h.2.2.1
  have hc : c ≠ 0 := by omega
  rw [abcRationalPoint_eq_div]
  exact ratDivNatCast_num hc h.coprime_left_right

/-- The reduced denominator of the point is the original summand. -/
theorem abcRationalPoint_den {a b c : Nat} (h : IsABCTriple a b c) :
    (abcRationalPoint a c).den = c := by
  have ha : 0 < a := h.1
  have hs : a + b = c := h.2.2.1
  have hc : c ≠ 0 := by omega
  rw [abcRationalPoint_eq_div]
  exact ratDivNatCast_den hc h.coprime_left_right

/-- The absolute value of the reduced numerator recovers `a`. -/
theorem abcRationalPoint_num_natAbs {a b c : Nat} (h : IsABCTriple a b c) :
    (abcRationalPoint a c).num.natAbs = a := by
  rw [abcRationalPoint_num h, Int.natAbs_natCast]

/-- The canonical reduced coordinates of a rational point are coprime. -/
theorem abcRationalPoint_reduced (a c : Nat) :
    Nat.Coprime (abcRationalPoint a c).num.natAbs (abcRationalPoint a c).den :=
  Rat.reduced _

/-- Recovering `Nat.Coprime a c` from the reduced coordinates is the genuine gcd consequence of
the dictionary: the reduced pair `(x.num.natAbs, x.den)` is `(a, c)`. -/
theorem abcRationalPoint_coordinate_coprime {a b c : Nat} (h : IsABCTriple a b c) :
    Nat.Coprime a c := by
  have hred : Nat.Coprime (abcRationalPoint a c).num.natAbs (abcRationalPoint a c).den :=
    abcRationalPoint_reduced a c
  rw [abcRationalPoint_num_natAbs h, abcRationalPoint_den h] at hred
  exact hred

/-- The third `{0, 1, ∞}` coordinate `x.den - x.num` is the missing summand `b`. -/
theorem abcRationalPoint_den_sub_num {a b c : Nat} (h : IsABCTriple a b c) :
    ((abcRationalPoint a c).den : Int) - (abcRationalPoint a c).num = (b : Int) := by
  have hs : a + b = c := h.2.2.1
  rw [abcRationalPoint_den h, abcRationalPoint_num h]
  have hcast : (c : Int) = (a : Int) + (b : Int) := by exact_mod_cast hs.symm
  omega

/-- The three `{0, 1, ∞}` coordinates `x.num.natAbs`, `(x.den - x.num).natAbs`, `x.den` of the
point are pairwise coprime.  Read through `abcRationalPoint_num_natAbs`,
`abcRationalPoint_den_sub_num` and `abcRationalPoint_den` this is exactly the imported
`IsABCTriple.pairwise_coprime`, which is reused here rather than re-proved. -/
theorem abcRationalPoint_coordinates_pairwise_coprime {a b c : Nat} (h : IsABCTriple a b c) :
    Nat.Coprime (abcRationalPoint a c).num.natAbs
        (((abcRationalPoint a c).den : Int) - (abcRationalPoint a c).num).natAbs ∧
      Nat.Coprime (abcRationalPoint a c).num.natAbs (abcRationalPoint a c).den ∧
        Nat.Coprime (((abcRationalPoint a c).den : Int) - (abcRationalPoint a c).num).natAbs
          (abcRationalPoint a c).den := by
  rw [abcRationalPoint_den_sub_num h, Int.natAbs_natCast, abcRationalPoint_num_natAbs h,
    abcRationalPoint_den h]
  exact h.pairwise_coprime

/-! ### 4. The point avoids `0` and `1` -/

theorem abcRationalPoint_ne_zero {a b c : Nat} (h : IsABCTriple a b c) :
    abcRationalPoint a c ≠ 0 := by
  have ha : 0 < a := h.1
  have hs : a + b = c := h.2.2.1
  have hc : c ≠ 0 := by omega
  have hcQ : (c : Rat) ≠ 0 := by exact_mod_cast hc
  have haQ : (a : Rat) ≠ 0 := by positivity
  rw [abcRationalPoint_eq_div]
  exact div_ne_zero haQ hcQ

theorem abcRationalPoint_ne_one {a b c : Nat} (h : IsABCTriple a b c) :
    abcRationalPoint a c ≠ 1 := by
  have ha : 0 < a := h.1
  have hb : 0 < b := h.2.1
  have hs : a + b = c := h.2.2.1
  have hc : c ≠ 0 := by omega
  have hcQ : (c : Rat) ≠ 0 := by exact_mod_cast hc
  have hac : (a : Rat) ≠ (c : Rat) := by
    intro hh
    have hac' : a = c := by exact_mod_cast hh
    omega
  rw [abcRationalPoint_eq_div]
  exact fun h1 => hac ((div_eq_one_iff_eq hcQ).mp h1)

/-! ### 5. Canonical Mathlib heights of the point -/

/-- The canonical Mathlib multiplicative height of the point `a / c` is `c`. -/
theorem abcRationalPoint_mulHeight₁ {a b c : Nat} (h : IsABCTriple a b c) :
    Height.mulHeight₁ (abcRationalPoint a c) = (c : Real) := by
  have ha : 0 < a := h.1
  have hs : a + b = c := h.2.2.1
  have hle : a ≤ c := by omega
  have hnum : (abcRationalPoint a c).num = (a : Int) := abcRationalPoint_num h
  have hden : (abcRationalPoint a c).den = c := abcRationalPoint_den h
  rw [Rat.mulHeight₁_eq_max, hnum, hden, Int.natAbs_natCast, max_eq_right hle]

/-- The canonical Mathlib logarithmic height of the point `a / c` is `Real.log c`. -/
theorem abcRationalPoint_logHeight₁ {a b c : Nat} (h : IsABCTriple a b c) :
    Height.logHeight₁ (abcRationalPoint a c) = Real.log (c : Real) := by
  have ha : 0 < a := h.1
  have hs : a + b = c := h.2.2.1
  have hle : a ≤ c := by omega
  have hmax : max (abcRationalPoint a c).num.natAbs (abcRationalPoint a c).den = c := by
    rw [abcRationalPoint_num h, abcRationalPoint_den h, Int.natAbs_natCast, max_eq_right hle]
  rw [Rat.logHeight₁_eq_log_max, hmax]

/-! ### 6. Finite prime support of the `{0, 1, ∞}` coordinates -/

/-- For a prime `p`, `p` divides `a * b * c` if and only if `p` divides one of the three
coordinate supports of the point: the reduced numerator `x.num.natAbs`, the difference
`(x.den - x.num).natAbs`, or the reduced denominator `x.den`.  These are exactly the finite
prime supports of `a`, `b`, `c`, and no conductor is introduced. -/
theorem prime_dvd_abc_iff_prime_dvd_point_coordinates {a b c p : Nat}
    (h : IsABCTriple a b c) (hp : p.Prime) :
    p ∣ a * b * c ↔
      p ∣ (abcRationalPoint a c).num.natAbs ∨
        p ∣ (((abcRationalPoint a c).den : Int) - (abcRationalPoint a c).num).natAbs ∨
          p ∣ (abcRationalPoint a c).den := by
  rw [abcRationalPoint_den_sub_num h, abcRationalPoint_num h, abcRationalPoint_den h,
    Int.natAbs_natCast, Int.natAbs_natCast]
  rw [Nat.Prime.dvd_mul hp, Nat.Prime.dvd_mul hp]
  tauto

/-- The radical factorization of the triple distributes prime divisibility of `radical (a*b*c)`
to the three radical factors. -/
theorem prime_dvd_radical_abc_iff {a b c p : Nat}
    (h : IsABCTriple a b c) (hp : p.Prime) :
    p ∣ radical (a * b * c) ↔ p ∣ radical a ∨ p ∣ radical b ∨ p ∣ radical c := by
  rw [h.radical_product_eq, Nat.Prime.dvd_mul hp, Nat.Prime.dvd_mul hp]
  tauto

end LeanFormal.IUT
