/-
  Canonical rational height decomposed into archimedean and finite-valuation contributions.

  Mathlib's canonical height of `q : ℚ` is multiplicative
  `Height.mulHeight₁ q = ↑(max q.num.natAbs q.den)` (`Rat.mulHeight₁_eq_max`) with logarithmic form
  `Height.logHeight₁ q = log ↑(max q.num.natAbs q.den)` (`Rat.logHeight₁_eq_log_max`).  This file
  expands the logarithmic height through `Nat.factorization`, `padicValRat` and `Real.log` into its
  standard local pieces:

  * `real_log_nat_eq_sum_factorization`, `real_log_nat_eq_sum_padicValNat`: for `n ≠ 0` the logarithm
    `log n` of a natural number is the finite sum `Σ_{p ∈ n.primeFactors} v_p(n) · log p` of its local
    contributions, where `v_p(n) = n.factorization p = padicValNat p n` for prime `p`;
  * `rational_logHeight₁_eq_max_zero_log_abs_add_den_factorization`: for `q ≠ 0`,
    `logHeight₁ q = max 0 (log |q|) + Σ_{p ∣ q.den} v_p(q.den) · log p`, one archimedean term
    `log⁺ |q|` plus the finite-valuation terms of the denominator;
  * `rational_logHeight₁_eq_max_zero_log_abs_add_den_padicValRat`: the same finite terms written with
    the actual local valuations of `q`, namely `max 0 (−v_p(q)) · log p` for `padicValRat p q`;
  * `rat_log_abs_eq_sum_padicValRat`: the product-formula shape `log |q| = Σ_p v_p(q) · log p` over
    the union of the numerator and denominator prime supports;
  * `divNatCast_logHeight₁_eq_max_log` and `divNatCast_logHeight₁_eq_den_factorization_of_le`: for
    coprime positive `a, b`,
    `logHeight₁ (a/b) = log (max a b) = max (log a) (log b) =
      max 0 (log (a/b)) + Σ_{p ∣ b} v_p(b) · log p`, with the pure denominator sum over
    `b.primeFactors` when `a ≤ b`.

  All statements concern the canonical Mathlib height (`Mathlib.NumberTheory.Height`) and the actual
  `Nat.factorization` / `padicValRat` data; nothing about ABC, IUT, or any estimate is assumed or
  introduced here.  The specialization to the project's actual ABC rational point and Frey/Legendre
  invariant `abcJInvariant` is in `LeanFormal.IUT.ABCBridge.Arithmetic.ABCInvariantLocalHeight`.
-/
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPointDictionary
import LeanFormal.IUT.ABCBridge.Arithmetic.ABCInvariantLocalValuations
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalBoundaryValuations
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.Data.Nat.Factorization.Basic

namespace LeanFormal.IUT

/-! ### Logarithms of natural numbers through `Nat.factorization` -/

/-- The logarithm of `max x y` of two positive reals is the maximum of the logarithms.  This is the
splitting step for the archimedean term of a rational height. -/
theorem real_log_max_of_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.log (max x y) = max (Real.log x) (Real.log y) := by
  rcases le_total x y with h | h
  · rw [max_eq_right h, max_eq_right (Real.log_le_log hx h)]
  · rw [max_eq_left h, max_eq_left (Real.log_le_log hy h)]

/-- The logarithm of a nonzero natural number is the finite sum of its `Nat.factorization`
contributions `v_p(n) · log p` over the prime factors of `n`. -/
theorem real_log_nat_eq_sum_factorization (n : ℕ) (hn : n ≠ 0) :
    Real.log (n : ℝ) = ∑ p ∈ n.primeFactors, (n.factorization p : ℝ) * Real.log p := by
  conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hn]
  rw [Nat.cast_prod]
  have hprod : (∏ p ∈ n.primeFactors, ((p ^ n.factorization p : ℕ) : ℝ)) =
      ∏ p ∈ n.primeFactors, (p : ℝ) ^ n.factorization p :=
    Finset.prod_congr rfl fun p _ => Nat.cast_pow p (n.factorization p)
  rw [hprod, Real.log_prod (fun p hp =>
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).pos.ne'))]
  exact Finset.sum_congr rfl fun p _ => Real.log_pow (p : ℝ) (n.factorization p)

/-- Variant of `real_log_nat_eq_sum_factorization` with `padicValNat` in place of `Nat.factorization`
(the two agree on primes). -/
theorem real_log_nat_eq_sum_padicValNat (n : ℕ) (hn : n ≠ 0) :
    Real.log (n : ℝ) = ∑ p ∈ n.primeFactors, (padicValNat p n : ℝ) * Real.log p := by
  rw [real_log_nat_eq_sum_factorization n hn]
  exact Finset.sum_congr rfl fun p hp => by
    rw [Nat.factorization_def n (Nat.prime_of_mem_primeFactors hp)]

/-! ### The archimedean logarithm of a rational number -/

/-- The archimedean logarithm of a nonzero rational number, in reduced coordinates: the logarithm of
its absolute value is `log |q.num| − log q.den`. -/
theorem rat_log_abs_eq_log_num_natAbs_sub_log_den (q : ℚ) (hq : q ≠ 0) :
    Real.log |(q : ℝ)| = Real.log (q.num.natAbs : ℝ) - Real.log (q.den : ℝ) := by
  have hqcast : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := by
    conv_lhs => rw [← Rat.num_div_den q]
    push_cast
    ring
  have hnumabs : |(q.num : ℝ)| = (q.num.natAbs : ℝ) := by
    rcases le_or_gt 0 q.num with h | h
    · rw [abs_of_nonneg (by exact_mod_cast h : (0 : ℝ) ≤ (q.num : ℝ)),
        ← Int.natAbs_of_nonneg h, Int.cast_natCast, Int.natAbs_natCast]
    · rw [abs_of_neg (by exact_mod_cast h : (q.num : ℝ) < 0), ← Int.cast_neg,
        ← Int.natAbs_of_nonneg (by omega : (0 : ℤ) ≤ -q.num), Int.natAbs_neg,
        Int.cast_natCast]
  have hnumne : (q.num.natAbs : ℝ) ≠ 0 := by
    exact_mod_cast Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr hq)
  have hdenne : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_nz
  rw [hqcast, abs_div, hnumabs, abs_of_pos (by exact_mod_cast q.den_pos)]
  exact Real.log_div hnumne hdenne

/-! ### Local valuations of a rational number -/

/-- Casting helper: the real cast of `(−z).toNat` is `max 0 (−z)`. -/
theorem int_toNat_neg_cast_eq_max_zero (z : ℤ) :
    ((-z).toNat : ℝ) = max 0 (-(z : ℝ)) := by
  rcases le_or_gt 0 z with hz | hz
  · rw [Int.toNat_eq_zero.mpr (by omega : -z ≤ 0),
      max_eq_left (neg_nonpos.mpr (by exact_mod_cast hz : (0 : ℝ) ≤ (z : ℝ)))]
    norm_num
  · have hnonneg : (0 : ℤ) ≤ -z := by omega
    have hcast : (((-z).toNat : ℕ) : ℝ) = (((-z).toNat : ℤ) : ℝ) := by rw [Int.cast_natCast]
    rw [hcast, Int.toNat_of_nonneg hnonneg,
      max_eq_right (neg_nonneg.mpr (by exact_mod_cast (le_of_lt hz) : (z : ℝ) ≤ 0))]
    simp

/-- The valuation of the reduced denominator is (the nonnegative part of) the negative of the
rational valuation: the finite-valuation terms of the height are the actual local terms
`max 0 (−v_p(q))`. -/
theorem rat_den_factorization_eq_neg_padicValRat_toNat (p : ℕ) (hp : p.Prime) (q : ℚ) :
    q.den.factorization p = (-(padicValRat p q)).toNat := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [Nat.factorization_def q.den hp]
  exact rational_den_padicValNat_eq_neg_padicValRat_toNat p q

/-- The logarithm of `|q|` as the finite sum of the local valuations of `q` over the union of the
numerator and denominator prime supports (the product-formula shape over the actual support). -/
theorem rat_log_abs_eq_sum_padicValRat (q : ℚ) (hq : q ≠ 0) :
    Real.log |(q : ℝ)| =
      ∑ p ∈ q.num.natAbs.primeFactors ∪ q.den.primeFactors,
        (padicValRat p q : ℝ) * Real.log p := by
  have hm : q.num.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr hq)
  have hn : q.den ≠ 0 := q.den_nz
  have hcop : Nat.Coprime q.num.natAbs q.den := Rat.reduced q
  have hdisj : Disjoint q.num.natAbs.primeFactors q.den.primeFactors := by
    rw [Finset.disjoint_left]
    exact fun p hpm hpn =>
      (Nat.prime_of_mem_primeFactors hpm).ne_one
        (Nat.eq_one_of_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd
          (Nat.mem_primeFactors.mp hpm).2.1 (Nat.mem_primeFactors.mp hpn).2.1))
  have hnum : ∑ p ∈ q.num.natAbs.primeFactors, (padicValRat p q : ℝ) * Real.log p =
      Real.log (q.num.natAbs : ℝ) := by
    rw [real_log_nat_eq_sum_factorization q.num.natAbs hm]
    exact Finset.sum_congr rfl fun p hpm => by
      have hp : p.Prime := Nat.prime_of_mem_primeFactors hpm
      haveI : Fact p.Prime := ⟨hp⟩
      have hpn : padicValNat p q.den = 0 := padicValNat.eq_zero_of_not_dvd fun hpn' =>
        not_coprime_of_prime_dvd_both hp hcop (Nat.mem_primeFactors.mp hpm).2.1 hpn'
      have hv : padicValRat p q = (q.num.natAbs.factorization p : ℤ) := by
        rw [padicValRat.eq_1 p q, padicValInt.eq_1 p q.num, hpn, Nat.cast_zero, sub_zero,
          Nat.factorization_def q.num.natAbs hp]
      rw [hv, Int.cast_natCast]
  have hden : ∑ p ∈ q.den.primeFactors, (padicValRat p q : ℝ) * Real.log p =
      - Real.log (q.den : ℝ) := by
    rw [real_log_nat_eq_sum_factorization q.den hn, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun p hpn => by
      have hp : p.Prime := Nat.prime_of_mem_primeFactors hpn
      haveI : Fact p.Prime := ⟨hp⟩
      have hpm : padicValNat p q.num.natAbs = 0 := padicValNat.eq_zero_of_not_dvd fun hpm' =>
        not_coprime_of_prime_dvd_both hp hcop hpm' (Nat.mem_primeFactors.mp hpn).2.1
      have hv : padicValRat p q = -(q.den.factorization p : ℤ) := by
        rw [padicValRat.eq_1 p q, padicValInt.eq_1 p q.num, hpm, Nat.cast_zero, zero_sub,
          Nat.factorization_def q.den hp]
      rw [hv, Int.cast_neg, Int.cast_natCast]
      ring
  rw [rat_log_abs_eq_log_num_natAbs_sub_log_den q hq, Finset.sum_union hdisj, hnum, hden]
  ring

/-! ### The canonical rational height as archimedean term plus finite valuations -/

/-- **Canonical rational height, decomposed.**  For `q ≠ 0` the logarithmic height is the
archimedean term `log⁺ |q| = max 0 (log |q|)` plus the finite-valuation terms `v_p(q.den) · log p`
over the prime factors of the denominator. -/
theorem rational_logHeight₁_eq_max_zero_log_abs_add_den_factorization (q : ℚ) (hq : q ≠ 0) :
    Height.logHeight₁ q = max 0 (Real.log |(q : ℝ)|) +
      ∑ p ∈ q.den.primeFactors, (q.den.factorization p : ℝ) * Real.log p := by
  have hmax : Real.log (max (q.num.natAbs : ℝ) (q.den : ℝ)) =
      max 0 (Real.log (q.num.natAbs : ℝ) - Real.log (q.den : ℝ)) + Real.log (q.den : ℝ) := by
    have hnum_abs_pos : (0 : ℝ) < (q.num.natAbs : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero
        (Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr hq))
    have hden_real_pos : (0 : ℝ) < (q.den : ℝ) := by exact_mod_cast q.den_pos
    rcases le_total (q.num.natAbs : ℝ) (q.den : ℝ) with hle | hle
    · rw [max_eq_right hle, max_eq_left (sub_nonpos.mpr (Real.log_le_log hnum_abs_pos hle))]
      ring
    · rw [max_eq_left hle, max_eq_right (sub_nonneg.mpr (Real.log_le_log hden_real_pos hle))]
      ring
  rw [Rat.logHeight₁_eq_log_max, Nat.cast_max, hmax,
    ← rat_log_abs_eq_log_num_natAbs_sub_log_den q hq,
    real_log_nat_eq_sum_factorization q.den q.den_nz]

/-- Intermediate form of the decomposition: archimedean term plus the logarithm of the reduced
denominator. -/
theorem rational_logHeight₁_eq_max_zero_log_abs_add_log_den (q : ℚ) (hq : q ≠ 0) :
    Height.logHeight₁ q = max 0 (Real.log |(q : ℝ)|) + Real.log (q.den : ℝ) := by
  rw [rational_logHeight₁_eq_max_zero_log_abs_add_den_factorization q hq,
    real_log_nat_eq_sum_factorization q.den q.den_nz]

/-- **Canonical rational height, fully in local terms.**  The finite-valuation terms are written with
the actual rational valuations of `q`: `max 0 (−v_p(q)) · log p`. -/
theorem rational_logHeight₁_eq_max_zero_log_abs_add_den_padicValRat (q : ℚ) (hq : q ≠ 0) :
    Height.logHeight₁ q = max 0 (Real.log |(q : ℝ)|) +
      ∑ p ∈ q.den.primeFactors, max 0 (-(padicValRat p q : ℝ)) * Real.log p := by
  rw [rational_logHeight₁_eq_max_zero_log_abs_add_den_factorization q hq]
  congr 1
  exact Finset.sum_congr rfl fun p hp => by
    rw [rat_den_factorization_eq_neg_padicValRat_toNat p (Nat.prime_of_mem_primeFactors hp) q,
      int_toNat_neg_cast_eq_max_zero (padicValRat p q)]

/-- When the archimedean term vanishes (`|q| ≤ 1`), the height is purely the sum of the local
denominator contributions. -/
theorem rational_logHeight₁_eq_sum_den_factorization_of_log_abs_nonpos (q : ℚ) (hq : q ≠ 0)
    (hlog : Real.log |(q : ℝ)| ≤ 0) :
    Height.logHeight₁ q =
      ∑ p ∈ q.den.primeFactors, (q.den.factorization p : ℝ) * Real.log p := by
  rw [rational_logHeight₁_eq_max_zero_log_abs_add_den_factorization q hq, max_eq_left hlog,
    zero_add]

/-- Vanishing-archimedean variant of `rational_logHeight₁_eq_max_zero_log_abs_add_den_padicValRat`. -/
theorem rational_logHeight₁_eq_sum_den_padicValRat_of_log_abs_nonpos (q : ℚ) (hq : q ≠ 0)
    (hlog : Real.log |(q : ℝ)| ≤ 0) :
    Height.logHeight₁ q =
      ∑ p ∈ q.den.primeFactors, max 0 (-(padicValRat p q : ℝ)) * Real.log p := by
  rw [rational_logHeight₁_eq_max_zero_log_abs_add_den_padicValRat q hq, max_eq_left hlog,
    zero_add]

/-- **Full local expansion of the height.**  Both the archimedean term (through the product-formula
sum of the local valuations of `q`) and the finite-valuation terms are expressed with `padicValRat`. -/
theorem rational_logHeight₁_eq_sum_all_places (q : ℚ) (hq : q ≠ 0) :
    Height.logHeight₁ q =
      max 0 (∑ p ∈ q.num.natAbs.primeFactors ∪ q.den.primeFactors,
          (padicValRat p q : ℝ) * Real.log p) +
        ∑ p ∈ q.den.primeFactors, max 0 (-(padicValRat p q : ℝ)) * Real.log p := by
  rw [rational_logHeight₁_eq_max_zero_log_abs_add_den_padicValRat q hq,
    rat_log_abs_eq_sum_padicValRat q hq]

/-! ### Coprime natural fractions `a / b` -/

/-- The multiplicative height of `a / b` for coprime naturals is `max a b`. -/
theorem divNatCast_mulHeight₁_eq_max (a b : ℕ) (hb : b ≠ 0) (hcop : Nat.Coprime a b) :
    Height.mulHeight₁ ((a : ℚ) / b) = max (a : ℝ) (b : ℝ) := by
  rw [Rat.mulHeight₁_eq_max, ratDivNatCast_num hb hcop, ratDivNatCast_den hb hcop,
    Int.natAbs_natCast, Nat.cast_max]

/-- The logarithmic height of `a / b` for coprime positive naturals is `log (max a b)`, i.e. the
maximum `max (log a) (log b)` of the two prime-factorization sums. -/
theorem divNatCast_logHeight₁_eq_max_log (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hcop : Nat.Coprime a b) :
    Height.logHeight₁ ((a : ℚ) / b) = max (Real.log a) (Real.log b) := by
  rw [Rat.logHeight₁_eq_log_max, ratDivNatCast_num hb.ne' hcop, ratDivNatCast_den hb.ne' hcop,
    Int.natAbs_natCast, Nat.cast_max]
  exact real_log_max_of_pos (by exact_mod_cast ha) (by exact_mod_cast hb)

/-- **Coprime-fraction height, decomposed.**  For coprime positive `a b`,
`logHeight₁ (a/b) = max 0 (log (a/b)) + Σ_{p ∣ b} v_p(b) · log p`: the archimedean term plus the
finite-valuation terms of the denominator. -/
theorem divNatCast_logHeight₁_eq_archimedean_add_den_factorization (a b : ℕ) (ha : 0 < a)
    (hb : 0 < b) (hcop : Nat.Coprime a b) :
    Height.logHeight₁ ((a : ℚ) / b) = max 0 (Real.log ((a : ℝ) / b)) +
      ∑ p ∈ b.primeFactors, (b.factorization p : ℝ) * Real.log p := by
  have hq : ((a : ℚ) / b) ≠ 0 := by
    exact div_ne_zero (by exact_mod_cast ha.ne') (by exact_mod_cast hb.ne')
  have habs : |(((a : ℚ) / (b : ℚ) : ℚ) : ℝ)| = (a : ℝ) / (b : ℝ) := by
    push_cast
    exact abs_of_pos (div_pos (by exact_mod_cast ha) (by exact_mod_cast hb))
  rw [rational_logHeight₁_eq_max_zero_log_abs_add_den_factorization ((a : ℚ) / b) hq,
    ratDivNatCast_den hb.ne' hcop, habs]

/-- Denominator-dominant case: for `a ≤ b` the archimedean term `max 0 (log (a/b))` vanishes and the
height is exactly the prime-factorization sum over the denominator. -/
theorem divNatCast_logHeight₁_eq_den_factorization_of_le (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hcop : Nat.Coprime a b) (hab : a ≤ b) :
    Height.logHeight₁ ((a : ℚ) / b) =
      ∑ p ∈ b.primeFactors, (b.factorization p : ℝ) * Real.log p := by
  rw [divNatCast_logHeight₁_eq_archimedean_add_den_factorization a b ha hb hcop]
  have hlog : Real.log ((a : ℝ) / b) ≤ 0 := by
    rw [Real.log_div (by exact_mod_cast ha.ne') (by exact_mod_cast hb.ne')]
    exact sub_nonpos.mpr (Real.log_le_log (by exact_mod_cast ha) (by exact_mod_cast hab))
  rw [max_eq_left hlog, zero_add]

/-- The denominator-dominant height with `padicValNat` weights: the `Σ_p v_p(b) log p` form. -/
theorem divNatCast_logHeight₁_eq_den_padicValNat_of_le (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hcop : Nat.Coprime a b) (hab : a ≤ b) :
    Height.logHeight₁ ((a : ℚ) / b) =
      ∑ p ∈ b.primeFactors, (padicValNat p b : ℝ) * Real.log p := by
  rw [divNatCast_logHeight₁_eq_den_factorization_of_le a b ha hb hcop hab]
  exact Finset.sum_congr rfl fun p hp => by
    rw [Nat.factorization_def b (Nat.prime_of_mem_primeFactors hp)]

end LeanFormal.IUT