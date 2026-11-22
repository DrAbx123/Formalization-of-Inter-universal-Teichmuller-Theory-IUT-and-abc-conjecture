/-
  Arithmetic boundary prime support: the finite set of primes where one of the two finite
  boundary valuations of a rational point is nonzero.

  For `x ≠ 0, 1` and a prime `p`, membership of `p` in the accepted
  `arithmeticPrimeSupport x` is equivalent to `padicValRat p x ≠ 0` or
  `padicValRat p (1 - x) ≠ 0`.  At the actual ABC point `abcRationalPoint a c` the three
  divisibility conditions `p ∣ a`, `p ∣ b`, `p ∣ c` are identified with the three nonzero
  boundary sign patterns.

  This is arithmetic support data.  It is deliberately *not* called a geometric conductor,
  and it does not prove the IUT IV Cor. 2.3 estimate.
-/
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalBoundaryValuations
import Mathlib.Tactic

namespace LeanFormal.IUT

/-! ## The accepted arithmetic support detected by boundary valuations -/

/-- Coordinate expansion of membership in the accepted `arithmeticPrimeSupport`. -/
theorem mem_arithmeticPrimeSupport_iff_dvd_coordinates {p : ℕ} (hp : Nat.Prime p) {x : ℚ}
    (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    p ∈ arithmeticPrimeSupport x ↔
      p ∣ x.num.natAbs ∨ p ∣ ((x.den : ℤ) - x.num).natAbs ∨ p ∣ x.den := by
  have hnum : x.num.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr hx0)
  have hgap : ((x.den : ℤ) - x.num).natAbs ≠ 0 :=
    Int.natAbs_ne_zero.mpr (by
      intro h0
      apply (sub_ne_zero.mpr (Ne.symm hx1) : (1 : ℚ) - x ≠ 0)
      rw [one_sub_eq_divInt_num_den x, h0, Rat.zero_divInt])
  have hden : x.den ≠ 0 := Rat.den_nz x
  unfold arithmeticPrimeSupport
  simp only [Finset.mem_union]
  constructor
  · intro hp
    rcases hp with (h | h) | h
    · exact Or.inl (Nat.mem_primeFactors.mp h).2.1
    · exact Or.inr (Or.inl (Nat.mem_primeFactors.mp h).2.1)
    · exact Or.inr (Or.inr (Nat.mem_primeFactors.mp h).2.1)
  · rintro (h | h | h)
    · exact Or.inl (Or.inl (Nat.mem_primeFactors.mpr ⟨hp, h, hnum⟩))
    · exact Or.inl (Or.inr (Nat.mem_primeFactors.mpr ⟨hp, h, hgap⟩))
    · exact Or.inr (Nat.mem_primeFactors.mpr ⟨hp, h, hden⟩)

/-- Every element of the arithmetic prime support is prime. -/
theorem prime_of_mem_arithmeticPrimeSupport {p : ℕ} {x : ℚ}
    (hp : p ∈ arithmeticPrimeSupport x) : Nat.Prime p := by
  unfold arithmeticPrimeSupport at hp
  simp only [Finset.mem_union] at hp
  rcases hp with (h | h) | h
  · exact Nat.prime_of_mem_primeFactors h
  · exact Nat.prime_of_mem_primeFactors h
  · exact Nat.prime_of_mem_primeFactors h

/-- Boundary-support theorem: for prime `p` and `x ≠ 0, 1`, the arithmetic prime support is
exactly the set of primes where one of the two finite boundary valuations is nonzero. -/
theorem mem_arithmeticPrimeSupport_iff_padicValRat_ne_zero {p : ℕ} (hp : Nat.Prime p) {x : ℚ}
    (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    p ∈ arithmeticPrimeSupport x ↔
      padicValRat p x ≠ 0 ∨ padicValRat p (1 - x) ≠ 0 := by
  rw [mem_arithmeticPrimeSupport_iff_dvd_coordinates hp hx0 hx1,
    padicValRat_ne_zero_iff_dvd_num_or_den hp hx0,
    padicValRat_one_sub_ne_zero_iff_dvd_gap_or_den hp hx1]
  tauto

/-- Complementary unramified/outside-support form: `p` is outside the arithmetic prime
support exactly when both boundary valuations vanish. -/
theorem not_mem_arithmeticPrimeSupport_iff_padicValRat_eq_zero {p : ℕ} (hp : Nat.Prime p)
    {x : ℚ} (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    p ∉ arithmeticPrimeSupport x ↔
      padicValRat p x = 0 ∧ padicValRat p (1 - x) = 0 := by
  rw [mem_arithmeticPrimeSupport_iff_padicValRat_ne_zero hp hx0 hx1]
  tauto

/-- The valuation-detected primes inside the arithmetic prime support exhaust it. -/
theorem filter_padicValRat_ne_zero_eq_arithmeticPrimeSupport {x : ℚ} (hx0 : x ≠ 0)
    (hx1 : x ≠ 1) :
    (arithmeticPrimeSupport x).filter
        (fun p => padicValRat p x ≠ 0 ∨ padicValRat p (1 - x) ≠ 0) =
      arithmeticPrimeSupport x := by
  ext p
  rw [Finset.mem_filter]
  constructor
  · exact fun h => h.1
  · intro hp
    exact ⟨hp, (mem_arithmeticPrimeSupport_iff_padicValRat_ne_zero
      (prime_of_mem_arithmeticPrimeSupport hp) hx0 hx1).mp hp⟩

/-- The accepted arithmetic weight as a finite sum over the primes detected by the two
finite boundary valuations. -/
theorem arithmeticWeight_eq_sum_log_boundaryValuationSupport {x : ℚ} (hx0 : x ≠ 0)
    (hx1 : x ≠ 1) :
    arithmeticWeight x =
      ∑ p ∈ (arithmeticPrimeSupport x).filter
        (fun p => padicValRat p x ≠ 0 ∨ padicValRat p (1 - x) ≠ 0), Real.log (p : ℝ) := by
  rw [filter_padicValRat_ne_zero_eq_arithmeticPrimeSupport hx0 hx1]
  rfl

/-! ## Specialization to the actual ABC rational point -/

/-- The `p`-adic valuation of `abcRationalPoint a c` is the difference of the valuations of
the numerator `a` and the denominator `c`. -/
theorem padicValRat_abcRationalPoint (p : ℕ) {a b c : ℕ} (h : IsABCTriple a b c) :
    padicValRat p (abcRationalPoint a c) =
      (padicValNat p a : ℤ) - (padicValNat p c : ℤ) := by
  rw [padicValRat_eq_natAbs_sub_den, abcRationalPoint_num_natAbs h, abcRationalPoint_den h]

/-- The `p`-adic valuation of `1 - abcRationalPoint a c` is the difference of the valuations
of the boundary gap `b` and the denominator `c`. -/
theorem padicValRat_one_sub_abcRationalPoint {p : ℕ} (hp : Nat.Prime p) {a b c : ℕ}
    (h : IsABCTriple a b c) :
    padicValRat p (1 - abcRationalPoint a c) =
      (padicValNat p b : ℤ) - (padicValNat p c : ℤ) := by
  rw [padicValRat_one_sub_eq_natAbs_sub_den hp (abcRationalPoint_ne_one h),
    abcRationalPoint_den_sub_num h, Int.natAbs_natCast, abcRationalPoint_den h]

/-- At the actual ABC point the three divisibility conditions `p ∣ a`, `p ∣ b`, `p ∣ c` are
exactly the three nonzero boundary sign patterns. -/
theorem abcRationalPoint_boundary_dvd_iff_pattern {p : ℕ} (hp : Nat.Prime p) {a b c : ℕ}
    (h : IsABCTriple a b c) :
    (p ∣ a ↔ 0 < padicValRat p (abcRationalPoint a c) ∧
              padicValRat p (1 - abcRationalPoint a c) = 0) ∧
    (p ∣ b ↔ padicValRat p (abcRationalPoint a c) = 0 ∧
              0 < padicValRat p (1 - abcRationalPoint a c)) ∧
    (p ∣ c ↔ padicValRat p (abcRationalPoint a c) < 0 ∧
              padicValRat p (1 - abcRationalPoint a c) =
                padicValRat p (abcRationalPoint a c)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have htriple := h
  obtain ⟨ha_pos, hb_pos, hsum, hab⟩ := htriple
  have ha0 : a ≠ 0 := by omega
  have hb0 : b ≠ 0 := by omega
  have hc0 : c ≠ 0 := by omega
  have hac : Nat.Coprime a c := by rw [← hsum]; exact coprime_add_left hab
  have hbc : Nat.Coprime b c := by rw [← hsum]; exact coprime_add_right hab
  have hvx := padicValRat_abcRationalPoint p h
  have hv1x := padicValRat_one_sub_abcRationalPoint hp h
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro hpa
      have hva : 0 < padicValNat p a := by
        have hne : padicValNat p a ≠ 0 := (dvd_iff_padicValNat_ne_zero ha0).mp hpa
        omega
      have hvc : padicValNat p c = 0 :=
        padicValNat.eq_zero_of_not_dvd (fun hpc =>
          not_coprime_of_prime_dvd_both hp hac hpa hpc)
      have hvb : padicValNat p b = 0 :=
        padicValNat.eq_zero_of_not_dvd (fun hpb =>
          not_coprime_of_prime_dvd_both hp hab hpa hpb)
      exact ⟨by rw [hvx]; omega, by rw [hv1x, hvb, hvc]; ring⟩
    · rintro ⟨hpos, -⟩
      rw [hvx] at hpos
      exact (dvd_iff_padicValNat_ne_zero ha0).mpr (by omega)
  · constructor
    · intro hpb
      have hvb : 0 < padicValNat p b := by
        have hne : padicValNat p b ≠ 0 := (dvd_iff_padicValNat_ne_zero hb0).mp hpb
        omega
      have hvc : padicValNat p c = 0 :=
        padicValNat.eq_zero_of_not_dvd (fun hpc =>
          not_coprime_of_prime_dvd_both hp hbc hpb hpc)
      have hva : padicValNat p a = 0 :=
        padicValNat.eq_zero_of_not_dvd (fun hpa =>
          not_coprime_of_prime_dvd_both hp hab hpa hpb)
      exact ⟨by rw [hvx, hva, hvc]; ring, by rw [hv1x]; omega⟩
    · rintro ⟨-, hpos⟩
      rw [hv1x] at hpos
      exact (dvd_iff_padicValNat_ne_zero hb0).mpr (by omega)
  · constructor
    · intro hpc
      have hvc : 0 < padicValNat p c := by
        have hne : padicValNat p c ≠ 0 := (dvd_iff_padicValNat_ne_zero hc0).mp hpc
        omega
      have hva : padicValNat p a = 0 :=
        padicValNat.eq_zero_of_not_dvd (fun hpa =>
          not_coprime_of_prime_dvd_both hp hac hpa hpc)
      have hvb : padicValNat p b = 0 :=
        padicValNat.eq_zero_of_not_dvd (fun hpb =>
          not_coprime_of_prime_dvd_both hp hbc hpb hpc)
      exact ⟨by rw [hvx, hva]; omega, by rw [hv1x, hvx, hva, hvb]⟩
    · rintro ⟨hneg, -⟩
      rw [hvx] at hneg
      exact (dvd_iff_padicValNat_ne_zero hc0).mpr (by omega)

/-- Boundary-support theorem at the actual ABC point. -/
theorem mem_arithmeticPrimeSupport_abcRationalPoint_iff_padicValRat_ne_zero {p : ℕ}
    (hp : Nat.Prime p) {a b c : ℕ} (h : IsABCTriple a b c) :
    p ∈ arithmeticPrimeSupport (abcRationalPoint a c) ↔
      padicValRat p (abcRationalPoint a c) ≠ 0 ∨
        padicValRat p (1 - abcRationalPoint a c) ≠ 0 :=
  mem_arithmeticPrimeSupport_iff_padicValRat_ne_zero hp (abcRationalPoint_ne_zero h)
    (abcRationalPoint_ne_one h)

/-- Complementary unramified form at the actual ABC point. -/
theorem not_mem_arithmeticPrimeSupport_abcRationalPoint_iff_padicValRat_eq_zero {p : ℕ}
    (hp : Nat.Prime p) {a b c : ℕ} (h : IsABCTriple a b c) :
    p ∉ arithmeticPrimeSupport (abcRationalPoint a c) ↔
      padicValRat p (abcRationalPoint a c) = 0 ∧
        padicValRat p (1 - abcRationalPoint a c) = 0 :=
  not_mem_arithmeticPrimeSupport_iff_padicValRat_eq_zero hp (abcRationalPoint_ne_zero h)
    (abcRationalPoint_ne_one h)

/-- The arithmetic weight at the actual ABC point, as a finite sum over the boundary
valuation support. -/
theorem arithmeticWeight_abcRationalPoint_eq_sum_log_boundaryValuationSupport {a b c : ℕ}
    (h : IsABCTriple a b c) :
    arithmeticWeight (abcRationalPoint a c) =
      ∑ p ∈ (arithmeticPrimeSupport (abcRationalPoint a c)).filter
        (fun p => padicValRat p (abcRationalPoint a c) ≠ 0 ∨
          padicValRat p (1 - abcRationalPoint a c) ≠ 0), Real.log (p : ℝ) :=
  arithmeticWeight_eq_sum_log_boundaryValuationSupport (abcRationalPoint_ne_zero h)
    (abcRationalPoint_ne_one h)

/-- The arithmetic weight at the actual ABC point, as a finite sum of `log p` over the
prime factors of `a * b * c`, using the accepted project radical identity. -/
theorem arithmeticWeight_abcRationalPoint_eq_sum_primeFactors_log {a b c : ℕ}
    (h : IsABCTriple a b c) :
    arithmeticWeight (abcRationalPoint a c) =
      ∑ p ∈ (a * b * c).primeFactors, Real.log (p : ℝ) := by
  rw [arithmeticWeight_abcRationalPoint h, natRadical_cast_log_eq_sum_primeFactors]

end LeanFormal.IUT
