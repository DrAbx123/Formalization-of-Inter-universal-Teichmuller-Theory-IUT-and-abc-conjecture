import LeanFormal.IUT.ABCBridge.Geometry.FreyOddReduction
import Mathlib.Algebra.Polynomial.Splits

/-!
# Split multiplicative reduction of the ABC Frey equation

This file uses the actual residue field of `ℤ_[p]` and Mathlib's
`HasSplitMultiplicativeReduction`.  The splitting polynomial is exactly the
polynomial in that definition, applied to the actual Frey equation.  The three
prime-support cases give the square parameters `b`, `-a`, and `a` respectively.
-/

noncomputable section

namespace LeanFormal.IUT

open Polynomial

open scoped WeierstrassCurve

/-- The actual residue field of the `p`-adic integers. -/
abbrev FreyResidueField (p : ℕ) [Fact p.Prime] := IsLocalRing.ResidueField ℤ_[p]

/-- The rational prime dies in the actual residue field. -/
theorem freyResidue_prime_eq_zero (p : ℕ) [Fact p.Prime] :
    (p : FreyResidueField p) = 0 := by
  have hmem : (p : ℤ_[p]) ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
    change (p : ℤ_[p]) ∈ nonunits ℤ_[p]
    exact PadicInt.p_nonunit
  have hzero := (IsLocalRing.residue_eq_zero_iff (p : ℤ_[p])).mpr hmem
  simpa only [map_natCast] using hzero

/-- The residue field has exactly the characteristic of the prime. -/
theorem freyResidue_charP (p : ℕ) [Fact p.Prime] : CharP (FreyResidueField p) p := by
  exact (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr
    (freyResidue_prime_eq_zero p)

/-- Natural coefficients vanish in this residue field exactly on prime support. -/
theorem freyResidue_natCast_eq_zero_iff (p n : ℕ) [Fact p.Prime] :
    (n : FreyResidueField p) = 0 ↔ p ∣ n := by
  letI := freyResidue_charP p
  exact CharP.cast_eq_zero_iff (FreyResidueField p) p n

/-- Odd residue characteristic retains two distinct tangent slopes. -/
theorem freyResidue_two_ne_zero {p : ℕ} [Fact p.Prime] (hp_two : p ≠ 2) :
    (2 : FreyResidueField p) ≠ 0 := by
  intro hzero
  have hdiv := (freyResidue_natCast_eq_zero_iff p 2).mp hzero
  rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with hone | htwo
  · exact (Fact.out : p.Prime).ne_one hone
  · exact hp_two htwo

/-- The literal splitting polynomial in Mathlib's split multiplicative
reduction definition, before reducing its coefficients. -/
def freyMultiplicativeSplittingPolynomial {R : Type*} [CommRing R] (a b : R) : R[X] :=
  let W := freyWeierstrassCurve a b
  C W.c₄ * X ^ 2 + C (W.a₁ * W.c₄) * X -
    C (54 * W.b₆ - 3 * W.b₂ * W.b₄ + W.a₂ * W.c₄)

/-- A closed formula obtained from the actual Weierstrass coefficients. -/
theorem freyMultiplicativeSplittingPolynomial_eq {R : Type*} [CommRing R] (a b : R) :
    freyMultiplicativeSplittingPolynomial a b =
      C (16 * (a ^ 2 + a * b + b ^ 2)) * X ^ 2 -
        C ((b - a) * (16 * (a ^ 2 + a * b + b ^ 2) + 24 * a * b)) := by
  simp only [freyMultiplicativeSplittingPolynomial, freyWeierstrassCurve_c₄,
    WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    freyWeierstrassCurve]
  simp only [zero_mul, mul_zero, add_zero, zero_add, zero_pow, OfNat.ofNat_ne_zero,
    C_0, Polynomial.C_mul, Polynomial.C_add, Polynomial.C_sub, Polynomial.C_neg,
    Polynomial.C_pow, Polynomial.C_ofNat, map_add, map_sub, map_mul, map_pow, map_ofNat]
  ring_nf

/-- The literal splitting polynomial commutes with the actual coefficient map. -/
theorem freyMultiplicativeSplittingPolynomial_map {R S : Type*}
    [CommRing R] [CommRing S] (f : R →+* S) (a b : R) :
    (freyMultiplicativeSplittingPolynomial a b).map f =
      freyMultiplicativeSplittingPolynomial (f a) (f b) := by
  simp only [freyMultiplicativeSplittingPolynomial_eq, Polynomial.map_sub,
    Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X,
    Polynomial.map_add, Polynomial.map_ofNat,
    map_mul, map_add, map_sub, map_pow, map_ofNat]

/-- With the first coordinate zero, the polynomial is the expected quadratic. -/
theorem freyMultiplicativeSplittingPolynomial_zero_left {R : Type*} [CommRing R]
    (b : R) :
    freyMultiplicativeSplittingPolynomial 0 b = C (16 * b ^ 2) * (X ^ 2 - C b) := by
  rw [freyMultiplicativeSplittingPolynomial_eq]
  simp only [zero_pow, OfNat.ofNat_ne_zero, zero_mul, mul_zero, zero_add,
    add_zero, sub_zero, map_mul, map_add, map_sub, map_pow, map_ofNat, C_0]
  ring_nf

/-- With the second coordinate zero, the parameter is minus the first. -/
theorem freyMultiplicativeSplittingPolynomial_zero_right {R : Type*} [CommRing R]
    (a : R) :
    freyMultiplicativeSplittingPolynomial a 0 = C (16 * a ^ 2) * (X ^ 2 - C (-a)) := by
  rw [freyMultiplicativeSplittingPolynomial_eq]
  simp only [zero_pow, OfNat.ofNat_ne_zero, zero_mul, mul_zero, add_zero,
    zero_sub, map_mul, map_add, map_sub, map_pow, map_neg, map_ofNat, C_0]
  ring_nf

/-- With `a+b=0`, translating the double root to zero gives parameter `a`. -/
theorem freyMultiplicativeSplittingPolynomial_neg_right {R : Type*} [CommRing R]
    (a : R) :
    freyMultiplicativeSplittingPolynomial a (-a) = C (16 * a ^ 2) * (X ^ 2 - C a) := by
  rw [freyMultiplicativeSplittingPolynomial_eq]
  simp only [map_mul, map_add, map_sub, map_neg, map_pow, map_ofNat]
  ring

/-- A monic quadratic of this shape splits exactly when its parameter has a
square root.  This uses the library's actual polynomial-splitting predicate. -/
theorem frey_quadratic_splits_iff_exists_square {K : Type*} [Field K] (d : K) :
    (X ^ 2 - C d : K[X]).Splits ↔ ∃ r : K, r ^ 2 = d := by
  constructor
  · intro hsplits
    have hdegree : (X ^ 2 - C d : K[X]).degree ≠ 0 := by
      intro hzero
      have hcoeff : (X ^ 2 - C d : K[X]).coeff 2 = 0 :=
        coeff_eq_zero_of_degree_lt (by rw [hzero]; norm_num)
      norm_num at hcoeff
    obtain ⟨r, hr⟩ := hsplits.exists_eval_eq_zero hdegree
    refine ⟨r, ?_⟩
    simpa only [eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] using hr
  · rintro ⟨r, hr⟩
    have hfactor : (X ^ 2 - C d : K[X]) = (X - C r) * (X + C r) := by
      rw [← hr, map_pow]
      ring
    rw [hfactor]
    exact (Polynomial.Splits.X_sub_C r).mul (Polynomial.Splits.X_add_C r)

/-- The nonzero `c₄` coefficient does not change the splitting criterion. -/
theorem frey_scaled_quadratic_splits_iff_exists_square {K : Type*} [Field K]
    (u d : K) (hu : u ≠ 0) :
    (C u * (X ^ 2 - C d) : K[X]).Splits ↔ ∃ r : K, r ^ 2 = d := by
  rw [Polynomial.splits_mul_iff_right (by simpa using hu) (Polynomial.Splits.C u)]
  exact frey_quadratic_splits_iff_exists_square d

/-- The actual `c₄` remains nonzero in the residue field on the prime support. -/
theorem freyResidue_c4_ne_zero_of_dvd {p a b c : ℕ} [Fact p.Prime]
    (h : IsABCTriple a b c) (hp_two : p ≠ 2) (hdiv : p ∣ a * b * c) :
    (freyWeierstrassCurve (a : FreyResidueField p) (b : FreyResidueField p)).c₄ ≠ 0 := by
  have hunit := (freyPadicIntegralModel_c4_isUnit_of_dvd h hp_two hdiv).map
    (IsLocalRing.residue ℤ_[p])
  simpa only [freyPadicIntegralModel, freyWeierstrassCurve_c₄,
    map_mul, map_add, map_pow, map_ofNat, map_natCast] using hunit.ne_zero

/-- The sum relation is preserved in the actual residue field. -/
theorem freyResidue_sum {p a b c : ℕ} [Fact p.Prime] (h : IsABCTriple a b c) :
    (a : FreyResidueField p) + (b : FreyResidueField p) = (c : FreyResidueField p) := by
  simpa only [Nat.cast_add] using
    congrArg (fun n : ℕ => (n : FreyResidueField p)) h.2.2.1

/-- In the `p|a` case the two other residues remain nonzero; primitivity enters
through the proved invariant-coprimality and `c₄`-unit theorem. -/
theorem freyResidue_units_of_dvd_left {p a b c : ℕ} [Fact p.Prime]
    (h : IsABCTriple a b c) (hp_two : p ≠ 2) (ha : p ∣ a) :
    (b : FreyResidueField p) ≠ 0 ∧ (c : FreyResidueField p) ≠ 0 := by
  have hazero := (freyResidue_natCast_eq_zero_iff p a).mpr ha
  have hc4 := freyResidue_c4_ne_zero_of_dvd h hp_two
    (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left ha b) c)
  have hb : (b : FreyResidueField p) ≠ 0 := by
    intro hbzero
    apply hc4
    simp [freyWeierstrassCurve_c₄, hazero, hbzero]
  refine ⟨hb, ?_⟩
  have hsum := freyResidue_sum (p := p) h
  have hbc : (b : FreyResidueField p) = (c : FreyResidueField p) := by
    simpa only [hazero, zero_add] using hsum
  exact fun hczero => hb (hbc.trans hczero)

/-- In the `p|b` case the other two residues remain nonzero. -/
theorem freyResidue_units_of_dvd_right {p a b c : ℕ} [Fact p.Prime]
    (h : IsABCTriple a b c) (hp_two : p ≠ 2) (hb : p ∣ b) :
    (a : FreyResidueField p) ≠ 0 ∧ (c : FreyResidueField p) ≠ 0 := by
  have hbzero := (freyResidue_natCast_eq_zero_iff p b).mpr hb
  have hc4 := freyResidue_c4_ne_zero_of_dvd h hp_two
    (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hb a) c)
  have ha : (a : FreyResidueField p) ≠ 0 := by
    intro hazero
    apply hc4
    simp [freyWeierstrassCurve_c₄, hazero, hbzero]
  refine ⟨ha, ?_⟩
  have hsum := freyResidue_sum (p := p) h
  have hac : (a : FreyResidueField p) = (c : FreyResidueField p) := by
    simpa only [hbzero, add_zero] using hsum
  exact fun hczero => ha (hac.trans hczero)

/-- At `p|c`, the residues satisfy `b=-a`, with both nonzero. -/
theorem freyResidue_units_of_dvd_sum {p a b c : ℕ} [Fact p.Prime]
    (h : IsABCTriple a b c) (hp_two : p ≠ 2) (hc : p ∣ c) :
    (b : FreyResidueField p) = -(a : FreyResidueField p) ∧
      (a : FreyResidueField p) ≠ 0 ∧ (b : FreyResidueField p) ≠ 0 := by
  have hczero := (freyResidue_natCast_eq_zero_iff p c).mpr hc
  have hsum := freyResidue_sum (p := p) h
  rw [hczero] at hsum
  have hneg : (b : FreyResidueField p) = -(a : FreyResidueField p) := by
    linear_combination hsum
  have hc4 := freyResidue_c4_ne_zero_of_dvd h hp_two (dvd_mul_of_dvd_right hc (a * b))
  have ha : (a : FreyResidueField p) ≠ 0 := by
    intro hazero
    apply hc4
    simp [freyWeierstrassCurve_c₄, hneg, hazero]
  exact ⟨hneg, ha, by simpa only [hneg, neg_ne_zero] using ha⟩

/-- The support alternatives are mutually exclusive, with every excluded
divisibility condition retained in the public conclusion. -/
theorem freyResidue_prime_support_cases {p a b c : ℕ} [Fact p.Prime]
    (h : IsABCTriple a b c) (hp_two : p ≠ 2) (hdiv : p ∣ a * b * c) :
    (p ∣ a ∧ ¬ p ∣ b ∧ ¬ p ∣ c) ∨
      (p ∣ b ∧ ¬ p ∣ a ∧ ¬ p ∣ c) ∨
      (p ∣ c ∧ ¬ p ∣ a ∧ ¬ p ∣ b) := by
  have hcases : p ∣ a ∨ p ∣ b ∨ p ∣ c := by
    simpa only [(Fact.out : p.Prime).dvd_mul, or_assoc] using hdiv
  rcases hcases with ha | hb | hc
  · obtain ⟨hbnonzero, hcnonzero⟩ := freyResidue_units_of_dvd_left h hp_two ha
    exact Or.inl ⟨ha, fun hb => hbnonzero ((freyResidue_natCast_eq_zero_iff p b).mpr hb),
      fun hc => hcnonzero ((freyResidue_natCast_eq_zero_iff p c).mpr hc)⟩
  · obtain ⟨hanonzero, hcnonzero⟩ := freyResidue_units_of_dvd_right h hp_two hb
    exact Or.inr (Or.inl ⟨hb, fun ha => hanonzero ((freyResidue_natCast_eq_zero_iff p a).mpr ha),
      fun hc => hcnonzero ((freyResidue_natCast_eq_zero_iff p c).mpr hc)⟩)
  · obtain ⟨_, hanonzero, hbnonzero⟩ := freyResidue_units_of_dvd_sum h hp_two hc
    exact Or.inr (Or.inr ⟨hc, fun ha => hanonzero ((freyResidue_natCast_eq_zero_iff p a).mpr ha),
      fun hb => hbnonzero ((freyResidue_natCast_eq_zero_iff p b).mpr hb)⟩)

/-- The chosen integral model in Mathlib is the explicit integral Frey model,
because the fraction-field coefficient map is injective. -/
theorem freyPadicCurve_integralModel_eq (p a b : ℕ) [Fact p.Prime]
    [WeierstrassCurve.IsIntegral ℤ_[p] (freyPadicCurve p a b)] :
    (freyPadicCurve p a b).integralModel ℤ_[p] = freyPadicIntegralModel p a b := by
  have hbase : ((freyPadicCurve p a b).integralModel ℤ_[p])⁄ℚ_[p] =
      (freyPadicIntegralModel p a b)⁄ℚ_[p] := by
    rw [WeierstrassCurve.baseChange_integralModel_eq, freyPadicIntegralModel_baseChange]
  ext
  · apply IsFractionRing.injective ℤ_[p] ℚ_[p]
    simpa only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁] using
      congrArg (fun W : WeierstrassCurve ℚ_[p] => W.a₁) hbase
  · apply IsFractionRing.injective ℤ_[p] ℚ_[p]
    simpa only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₂] using
      congrArg (fun W : WeierstrassCurve ℚ_[p] => W.a₂) hbase
  · apply IsFractionRing.injective ℤ_[p] ℚ_[p]
    simpa only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₃] using
      congrArg (fun W : WeierstrassCurve ℚ_[p] => W.a₃) hbase
  · apply IsFractionRing.injective ℤ_[p] ℚ_[p]
    simpa only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₄] using
      congrArg (fun W : WeierstrassCurve ℚ_[p] => W.a₄) hbase
  · apply IsFractionRing.injective ℤ_[p] ℚ_[p]
    simpa only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₆] using
      congrArg (fun W : WeierstrassCurve ℚ_[p] => W.a₆) hbase

/-- The actual split-reduction class is equivalent to splitting its literal
residue polynomial; actual multiplicative reduction is supplied beforehand. -/
theorem freyPadicCurve_hasSplitMultiplicativeReduction_iff_polynomial
    {p a b c : ℕ} [Fact p.Prime] (h : IsABCTriple a b c) (hp_two : p ≠ 2)
    (hdiv : p ∣ a * b * c) :
    WeierstrassCurve.HasSplitMultiplicativeReduction ℤ_[p] (freyPadicCurve p a b) ↔
      (freyMultiplicativeSplittingPolynomial (a : FreyResidueField p)
        (b : FreyResidueField p)).Splits := by
  have hmult := freyPadicCurve_hasMultiplicativeReduction_of_dvd h hp_two hdiv
  letI : WeierstrassCurve.IsMinimal ℤ_[p] (freyPadicCurve p a b) := hmult.toIsMinimal
  constructor
  · intro hsplit
    have hpoly := hsplit.splitMultiplicativeReduction
    rw [freyPadicCurve_integralModel_eq] at hpoly
    change ((freyMultiplicativeSplittingPolynomial (a : ℤ_[p]) (b : ℤ_[p])).map
      (algebraMap ℤ_[p] (FreyResidueField p))).Splits at hpoly
    rw [freyMultiplicativeSplittingPolynomial_map] at hpoly
    simpa only [map_natCast] using hpoly
  · intro hpoly
    haveI : WeierstrassCurve.HasMultiplicativeReduction ℤ_[p] (freyPadicCurve p a b) := hmult
    refine WeierstrassCurve.HasSplitMultiplicativeReduction.mk ?_
    rw [freyPadicCurve_integralModel_eq]
    change ((freyMultiplicativeSplittingPolynomial (a : ℤ_[p]) (b : ℤ_[p])).map
      (algebraMap ℤ_[p] (FreyResidueField p))).Splits
    rw [freyMultiplicativeSplittingPolynomial_map]
    simpa only [map_natCast] using hpoly

/-- Nonzero branch parameters give a nonzero scalar factor in the actual
splitting polynomial. -/
theorem freyResidue_sixteen_mul_square_ne_zero {p : ℕ} [Fact p.Prime]
    (hp_two : p ≠ 2) {d : FreyResidueField p} (hd : d ≠ 0) :
    16 * d ^ 2 ≠ 0 := by
  have hsixteen : (16 : FreyResidueField p) ≠ 0 := by
    convert pow_ne_zero 4 (freyResidue_two_ne_zero hp_two) using 1 <;> norm_num
  exact mul_ne_zero hsixteen (pow_ne_zero 2 hd)

/-- At `p|a`, actual split multiplicative reduction is equivalent to the
residue of `b` having a square root. -/
theorem freyPadicCurve_hasSplitMultiplicativeReduction_iff_of_dvd_left
    {p a b c : ℕ} [Fact p.Prime] (h : IsABCTriple a b c) (hp_two : p ≠ 2)
    (ha : p ∣ a) :
    WeierstrassCurve.HasSplitMultiplicativeReduction ℤ_[p] (freyPadicCurve p a b) ↔
      ∃ r : FreyResidueField p, r ^ 2 = (b : FreyResidueField p) := by
  have hdiv : p ∣ a * b * c := dvd_mul_of_dvd_left (dvd_mul_of_dvd_left ha b) c
  rw [freyPadicCurve_hasSplitMultiplicativeReduction_iff_polynomial h hp_two hdiv,
    (freyResidue_natCast_eq_zero_iff p a).mpr ha,
    freyMultiplicativeSplittingPolynomial_zero_left]
  exact frey_scaled_quadratic_splits_iff_exists_square _ _
    (freyResidue_sixteen_mul_square_ne_zero hp_two
      (freyResidue_units_of_dvd_left h hp_two ha).1)

/-- At `p|b`, the square-root parameter is the residue of `-a`. -/
theorem freyPadicCurve_hasSplitMultiplicativeReduction_iff_of_dvd_right
    {p a b c : ℕ} [Fact p.Prime] (h : IsABCTriple a b c) (hp_two : p ≠ 2)
    (hb : p ∣ b) :
    WeierstrassCurve.HasSplitMultiplicativeReduction ℤ_[p] (freyPadicCurve p a b) ↔
      ∃ r : FreyResidueField p, r ^ 2 = -(a : FreyResidueField p) := by
  have hdiv : p ∣ a * b * c := dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hb a) c
  rw [freyPadicCurve_hasSplitMultiplicativeReduction_iff_polynomial h hp_two hdiv,
    (freyResidue_natCast_eq_zero_iff p b).mpr hb,
    freyMultiplicativeSplittingPolynomial_zero_right]
  exact frey_scaled_quadratic_splits_iff_exists_square _ _
    (freyResidue_sixteen_mul_square_ne_zero hp_two
      (freyResidue_units_of_dvd_right h hp_two hb).1)

/-- At `p|c`, the double root is `a` and its tangent parameter is the residue of `a`. -/
theorem freyPadicCurve_hasSplitMultiplicativeReduction_iff_of_dvd_sum
    {p a b c : ℕ} [Fact p.Prime] (h : IsABCTriple a b c) (hp_two : p ≠ 2)
    (hc : p ∣ c) :
    WeierstrassCurve.HasSplitMultiplicativeReduction ℤ_[p] (freyPadicCurve p a b) ↔
      ∃ r : FreyResidueField p, r ^ 2 = (a : FreyResidueField p) := by
  have hdiv : p ∣ a * b * c := dvd_mul_of_dvd_right hc (a * b)
  obtain ⟨hneg, hanonzero, _⟩ := freyResidue_units_of_dvd_sum h hp_two hc
  rw [freyPadicCurve_hasSplitMultiplicativeReduction_iff_polynomial h hp_two hdiv,
    hneg, freyMultiplicativeSplittingPolynomial_neg_right]
  exact frey_scaled_quadratic_splits_iff_exists_square _ _
    (freyResidue_sixteen_mul_square_ne_zero hp_two hanonzero)

/-- The scalar equation used below is the literal affine equation of the
actual Weierstrass coefficients, with all terms moved to the left. -/
theorem freyAffineEquation_residual_factorization {R : Type*} [CommRing R]
    (a b x y : R) :
    let W := freyWeierstrassCurve a b
    y ^ 2 + W.a₁ * x * y + W.a₃ * y -
      (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) =
        y ^ 2 - x * (x - a) * (x + b) := by
  simp only [freyWeierstrassCurve, zero_mul, zero_add, add_zero]
  ring

/-- At the double root `(0,0)` when `p|a`, the exact local equation has
quadratic part `y²-bx²` and cubic remainder `-x³`. -/
theorem freyResidue_tangent_expansion_of_dvd_left {p a b : ℕ} [Fact p.Prime]
    (ha : p ∣ a) (x y : FreyResidueField p) :
    let W := freyWeierstrassCurve (a : FreyResidueField p) (b : FreyResidueField p)
    y ^ 2 + W.a₁ * x * y + W.a₃ * y -
      (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) =
        (y ^ 2 - (b : FreyResidueField p) * x ^ 2) - x ^ 3 := by
  dsimp only
  rw [freyAffineEquation_residual_factorization,
    (freyResidue_natCast_eq_zero_iff p a).mpr ha]
  ring

/-- At the double root `(0,0)` when `p|b`, the quadratic part is `y²+ax²`. -/
theorem freyResidue_tangent_expansion_of_dvd_right {p a b : ℕ} [Fact p.Prime]
    (hb : p ∣ b) (x y : FreyResidueField p) :
    let W := freyWeierstrassCurve (a : FreyResidueField p) (b : FreyResidueField p)
    y ^ 2 + W.a₁ * x * y + W.a₃ * y -
      (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) =
        (y ^ 2 + (a : FreyResidueField p) * x ^ 2) - x ^ 3 := by
  dsimp only
  rw [freyAffineEquation_residual_factorization,
    (freyResidue_natCast_eq_zero_iff p b).mpr hb]
  ring

/-- At `p|c`, translating the actual double root `(a,0)` by `x=a+z`
gives quadratic part `y²-az²` and cubic remainder `-z³`. -/
theorem freyResidue_tangent_expansion_of_dvd_sum {p a b c : ℕ} [Fact p.Prime]
    (h : IsABCTriple a b c) (hp_two : p ≠ 2) (hc : p ∣ c)
    (z y : FreyResidueField p) :
    let W := freyWeierstrassCurve (a : FreyResidueField p) (b : FreyResidueField p)
    let x := (a : FreyResidueField p) + z
    y ^ 2 + W.a₁ * x * y + W.a₃ * y -
      (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) =
        (y ^ 2 - (a : FreyResidueField p) * z ^ 2) - z ^ 3 := by
  dsimp only
  rw [freyAffineEquation_residual_factorization,
    (freyResidue_units_of_dvd_sum h hp_two hc).1]
  ring

/-- An actual square root factors the homogeneous quadratic tangent cone. -/
theorem frey_tangent_factorization_of_square {K : Type*} [Field K]
    {d r : K} (hr : r ^ 2 = d) (x y : K) :
    y ^ 2 - d * x ^ 2 = (y - r * x) * (y + r * x) := by
  rw [← hr]
  ring

/-- The two tangent slopes are distinct precisely under the nonzero-parameter
and odd-characteristic conditions needed in the three primitive ABC cases. -/
theorem frey_tangent_square_roots_distinct {K : Type*} [Field K]
    (htwo : (2 : K) ≠ 0) {d r : K} (hd : d ≠ 0) (hr : r ^ 2 = d) :
    r ≠ -r := by
  have hrnonzero : r ≠ 0 := by
    intro hzero
    apply hd
    rw [← hr, hzero]
    simp
  intro heq
  have hproduct : (2 : K) * r = 0 := by linear_combination heq
  exact mul_ne_zero htwo hrnonzero hproduct

/-- After an actual field map and an actual square-root witness, the literal
splitting polynomial factors into its two linear tangent factors. -/
theorem frey_scaled_quadratic_map_factorization {K L : Type*} [Field K] [Field L]
    (f : K →+* L) (u d : K) (r : L) (hr : r ^ 2 = f d) :
    (C u * (X ^ 2 - C d) : K[X]).map f =
      C (f u) * (X - C r) * (X + C r) := by
  simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_pow,
    Polynomial.map_C, Polynomial.map_X]
  rw [← hr, map_pow]
  ring

/-- The extension transport includes the actual polynomial, its splitting,
and distinct slopes, not a replacement Boolean for split reduction. -/
theorem frey_scaled_quadratic_map_splits_with_distinct_slopes
    {K L : Type*} [Field K] [Field L] (f : K →+* L)
    (htwo : (2 : K) ≠ 0) (u d : K) (hd : d ≠ 0)
    (r : L) (hr : r ^ 2 = f d) :
    (C u * (X ^ 2 - C d) : K[X]).map f =
        C (f u) * (X - C r) * (X + C r) ∧
      ((C u * (X ^ 2 - C d) : K[X]).map f).Splits ∧ r ≠ -r := by
  have hfactor := frey_scaled_quadratic_map_factorization f u d r hr
  have htwoL : (2 : L) ≠ 0 := by
    intro hzero
    apply htwo
    apply f.injective
    simpa only [map_ofNat, map_zero] using hzero
  have hdL : f d ≠ 0 := by
    intro hzero
    apply hd
    apply f.injective
    simpa only [map_zero] using hzero
  refine ⟨hfactor, ?_, frey_tangent_square_roots_distinct htwoL hdL hr⟩
  rw [hfactor]
  exact ((Polynomial.Splits.C (f u)).mul (Polynomial.Splits.X_sub_C r)).mul
    (Polynomial.Splits.X_add_C r)

/-- A finite residue extension containing a square root of `b` splits the
actual `p|a` polynomial, with two distinct tangent slopes.  No lift of the
residue extension to a valued field is asserted here. -/
theorem freyResidue_split_over_extension_of_dvd_left {p a b c : ℕ} [Fact p.Prime]
    (h : IsABCTriple a b c) (hp_two : p ≠ 2) (ha : p ∣ a)
    (L : Type*) [Field L] [Algebra (FreyResidueField p) L]
    [FiniteDimensional (FreyResidueField p) L]
    (r : L) (hr : r ^ 2 = algebraMap (FreyResidueField p) L (b : FreyResidueField p)) :
    ((freyMultiplicativeSplittingPolynomial (a : FreyResidueField p)
        (b : FreyResidueField p)).map (algebraMap (FreyResidueField p) L)).Splits ∧
      r ≠ -r := by
  rw [(freyResidue_natCast_eq_zero_iff p a).mpr ha,
    freyMultiplicativeSplittingPolynomial_zero_left]
  exact (frey_scaled_quadratic_map_splits_with_distinct_slopes
    (algebraMap (FreyResidueField p) L) (freyResidue_two_ne_zero hp_two)
    (16 * (b : FreyResidueField p) ^ 2) (b : FreyResidueField p)
    (freyResidue_units_of_dvd_left h hp_two ha).1 r hr).2

/-- In the `p|b` case the finite residue extension must contain a square root
of the actual parameter `-a`. -/
theorem freyResidue_split_over_extension_of_dvd_right {p a b c : ℕ} [Fact p.Prime]
    (h : IsABCTriple a b c) (hp_two : p ≠ 2) (hb : p ∣ b)
    (L : Type*) [Field L] [Algebra (FreyResidueField p) L]
    [FiniteDimensional (FreyResidueField p) L]
    (r : L) (hr : r ^ 2 = algebraMap (FreyResidueField p) L (-(a : FreyResidueField p))) :
    ((freyMultiplicativeSplittingPolynomial (a : FreyResidueField p)
        (b : FreyResidueField p)).map (algebraMap (FreyResidueField p) L)).Splits ∧
      r ≠ -r := by
  rw [(freyResidue_natCast_eq_zero_iff p b).mpr hb,
    freyMultiplicativeSplittingPolynomial_zero_right]
  exact (frey_scaled_quadratic_map_splits_with_distinct_slopes
    (algebraMap (FreyResidueField p) L) (freyResidue_two_ne_zero hp_two)
    (16 * (a : FreyResidueField p) ^ 2) (-(a : FreyResidueField p))
    (neg_ne_zero.mpr (freyResidue_units_of_dvd_right h hp_two hb).1) r hr).2

/-- In the `p|c` case the translated double root has square-root parameter `a`. -/
theorem freyResidue_split_over_extension_of_dvd_sum {p a b c : ℕ} [Fact p.Prime]
    (h : IsABCTriple a b c) (hp_two : p ≠ 2) (hc : p ∣ c)
    (L : Type*) [Field L] [Algebra (FreyResidueField p) L]
    [FiniteDimensional (FreyResidueField p) L]
    (r : L) (hr : r ^ 2 = algebraMap (FreyResidueField p) L (a : FreyResidueField p)) :
    ((freyMultiplicativeSplittingPolynomial (a : FreyResidueField p)
        (b : FreyResidueField p)).map (algebraMap (FreyResidueField p) L)).Splits ∧
      r ≠ -r := by
  obtain ⟨hneg, hanonzero, _⟩ := freyResidue_units_of_dvd_sum h hp_two hc
  rw [hneg, freyMultiplicativeSplittingPolynomial_neg_right]
  exact (frey_scaled_quadratic_map_splits_with_distinct_slopes
    (algebraMap (FreyResidueField p) L) (freyResidue_two_ne_zero hp_two)
    (16 * (a : FreyResidueField p) ^ 2) (a : FreyResidueField p)
    hanonzero r hr).2

end LeanFormal.IUT
