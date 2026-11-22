import LeanFormal.IUT.ABCBridge.Geometry.ABCResidueDiscriminant
import LeanFormal.IUT.ABCBridge.Arithmetic.ABCInvariantCoprimality
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction

/-!
# Odd-prime reduction of the actual ABC Frey equation

The integral and fraction-field models below are the established Frey equation
over `ℤ_[p]` and `ℚ_[p]`.  Statements about minimality quantify over Mathlib's
actual changes of Weierstrass variables.  Reduction classifications use
`WeierstrassCurve.HasGoodReduction` and `HasMultiplicativeReduction`.
-/

noncomputable section

namespace LeanFormal.IUT

open scoped WeierstrassCurve WithZero

/-- The actual integral ABC equation over the `p`-adic integers. -/
def freyPadicIntegralModel (p a b : ℕ) [Fact p.Prime] : WeierstrassCurve ℤ_[p] :=
  freyWeierstrassCurve (a : ℤ_[p]) (b : ℤ_[p])

/-- The generic fibre of the integral ABC equation over the `p`-adic field. -/
def freyPadicCurve (p a b : ℕ) [Fact p.Prime] : WeierstrassCurve ℚ_[p] :=
  freyWeierstrassCurve (a : ℚ_[p]) (b : ℚ_[p])

/-- The integral `p`-adic model comes from the actual integer coefficients. -/
theorem freyPadicIntegralModel_eq_int_map (p a b : ℕ) [Fact p.Prime] :
    freyPadicIntegralModel p a b =
      (freyWeierstrassCurve (a : ℤ) (b : ℤ)).map (Int.castRingHom ℤ_[p]) := by
  rw [freyWeierstrassCurve_map]
  simp only [map_natCast, freyPadicIntegralModel]

/-- Passing to the fraction field gives the actual Frey curve over `ℚ_[p]`. -/
theorem freyPadicIntegralModel_baseChange (p a b : ℕ) [Fact p.Prime] :
    (freyPadicIntegralModel p a b)⁄ℚ_[p] = freyPadicCurve p a b := by
  change (freyWeierstrassCurve (a : ℤ_[p]) (b : ℤ_[p])).map
    (algebraMap ℤ_[p] ℚ_[p]) = freyWeierstrassCurve (a : ℚ_[p]) (b : ℚ_[p])
  rw [freyWeierstrassCurve_map]
  simp only [map_natCast]

/-- Integrality is witnessed by the explicitly constructed `p`-adic model. -/
theorem freyPadicCurve_isIntegral (p a b : ℕ) [Fact p.Prime] :
    WeierstrassCurve.IsIntegral ℤ_[p] (freyPadicCurve p a b) := by
  exact ⟨⟨freyPadicIntegralModel p a b,
    (freyPadicIntegralModel_baseChange p a b).symm⟩⟩

/-- The actual discriminant of the integral model is the cast of `16(abc)²`. -/
theorem freyPadicIntegralModel_discriminant {p a b c : ℕ} [Fact p.Prime]
    (hsum : a + b = c) :
    (freyPadicIntegralModel p a b).Δ = ((16 * (a * b * c) ^ 2 : ℕ) : ℤ_[p]) := by
  have hcast : (a : ℤ_[p]) + (b : ℤ_[p]) = (c : ℤ_[p]) := by
    simpa only [Nat.cast_add] using congrArg (fun n : ℕ => (n : ℤ_[p])) hsum
  rw [freyPadicIntegralModel, freyWeierstrassCurve_discriminant, hcast]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  ring

/-- The generic fibre has the same integral discriminant formula. -/
theorem freyPadicCurve_discriminant {p a b c : ℕ} [Fact p.Prime]
    (hsum : a + b = c) :
    (freyPadicCurve p a b).Δ = ((16 * (a * b * c) ^ 2 : ℕ) : ℚ_[p]) := by
  have hcast : (a : ℚ_[p]) + (b : ℚ_[p]) = (c : ℚ_[p]) := by
    simpa only [Nat.cast_add] using congrArg (fun n : ℕ => (n : ℚ_[p])) hsum
  rw [freyPadicCurve, freyWeierstrassCurve_discriminant, hcast]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  ring

/-- Integer coefficients are units exactly when the prime does not divide them. -/
theorem freyPadic_natCast_isUnit_iff (p n : ℕ) [Fact p.Prime] :
    IsUnit (n : ℤ_[p]) ↔ ¬ p ∣ n := by
  rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
  exact (Fact.out : p.Prime).coprime_iff_not_dvd

/-- The discriminant-unit condition is an actual unit condition in `ℤ_[p]`. -/
theorem freyPadicIntegralModel_discriminant_isUnit_iff {p a b c : ℕ}
    [Fact p.Prime] (hsum : a + b = c) (hp_two : p ≠ 2) :
    IsUnit (freyPadicIntegralModel p a b).Δ ↔ ¬ p ∣ a * b * c := by
  rw [freyPadicIntegralModel_discriminant hsum, freyPadic_natCast_isUnit_iff]
  exact not_congr
    ((abcResidueDiscriminant_eq_zero_iff_dvd_discriminant a b c p).symm.trans
      (abcResidueDiscriminant_eq_zero_iff (Fact.out : p.Prime) hp_two))

/-- The complementary discriminant condition is also exact inside `ℤ_[p]`. -/
theorem freyPadicIntegralModel_discriminant_not_isUnit_iff {p a b c : ℕ}
    [Fact p.Prime] (hsum : a + b = c) (hp_two : p ≠ 2) :
    ¬ IsUnit (freyPadicIntegralModel p a b).Δ ↔ p ∣ a * b * c := by
  simpa only [not_not] using not_congr
    (freyPadicIntegralModel_discriminant_isUnit_iff hsum hp_two)

/-- The norm formulation of the nonunit discriminant condition. -/
theorem freyPadicIntegralModel_discriminant_norm_lt_one_iff {p a b c : ℕ}
    [Fact p.Prime] (hsum : a + b = c) (hp_two : p ≠ 2) :
    ‖(freyPadicIntegralModel p a b).Δ‖ < 1 ↔ p ∣ a * b * c := by
  rw [← PadicInt.not_isUnit_iff]
  exact freyPadicIntegralModel_discriminant_not_isUnit_iff hsum hp_two

/-- The discrete valuation used by Mathlib's minimal-model reduction predicates. -/
abbrev freyPadicValuation (p : ℕ) [Fact p.Prime] : Valuation ℚ_[p] ℤᵐ⁰ :=
  IsDedekindDomain.HeightOneSpectrum.valuation ℚ_[p]
    (IsDiscreteValuationRing.maximalIdeal ℤ_[p])

/-- A `p`-adic integral unit has value one for this precise DVR valuation. -/
theorem freyPadicValuation_eq_one_of_isUnit {p : ℕ} [Fact p.Prime]
    {z : ℤ_[p]} (hz : IsUnit z) :
    freyPadicValuation p (algebraMap ℤ_[p] ℚ_[p] z) = 1 := by
  apply le_antisymm
  · exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one
      (IsDiscreteValuationRing.maximalIdeal ℤ_[p]) z
  · apply le_of_not_gt
    intro hlt
    have hmem : z ∈ IsLocalRing.maximalIdeal ℤ_[p] :=
      (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem _ _).mp hlt
    have hnorm := PadicInt.isUnit_iff.mp hz
    rw [IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits, hnorm] at hmem
    exact lt_irrefl 1 hmem

/-- Nonunits have value strictly below one for the same DVR valuation. -/
theorem freyPadicValuation_lt_one_iff_not_isUnit {p : ℕ} [Fact p.Prime]
    (z : ℤ_[p]) :
    freyPadicValuation p (algebraMap ℤ_[p] ℚ_[p] z) < 1 ↔ ¬ IsUnit z := by
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem]
  change z ∈ IsLocalRing.maximalIdeal ℤ_[p] ↔ ¬ IsUnit z
  rw [IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits, PadicInt.not_isUnit_iff]

/-- The generic-fibre discriminant is exactly the image of the integral one. -/
theorem freyPadicCurve_discriminant_eq_map_integral (p a b : ℕ) [Fact p.Prime] :
    (freyPadicCurve p a b).Δ =
      algebraMap ℤ_[p] ℚ_[p] (freyPadicIntegralModel p a b).Δ := by
  rw [← freyPadicIntegralModel_baseChange p a b,
    WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ]

/-- Off `abc`, the actual generic-fibre discriminant has DVR value one. -/
theorem freyPadicCurve_discriminant_valuation_eq_one {p a b c : ℕ}
    [Fact p.Prime] (hsum : a + b = c) (hp_two : p ≠ 2)
    (hnot : ¬ p ∣ a * b * c) :
    freyPadicValuation p (freyPadicCurve p a b).Δ = 1 := by
  rw [freyPadicCurve_discriminant_eq_map_integral]
  exact freyPadicValuation_eq_one_of_isUnit
    ((freyPadicIntegralModel_discriminant_isUnit_iff hsum hp_two).mpr hnot)

/-- On `abc`, the actual generic-fibre discriminant has value strictly below one. -/
theorem freyPadicCurve_discriminant_valuation_lt_one_iff {p a b c : ℕ}
    [Fact p.Prime] (hsum : a + b = c) (hp_two : p ≠ 2) :
    freyPadicValuation p (freyPadicCurve p a b).Δ < 1 ↔ p ∣ a * b * c := by
  rw [freyPadicCurve_discriminant_eq_map_integral,
    freyPadicValuation_lt_one_iff_not_isUnit]
  exact freyPadicIntegralModel_discriminant_not_isUnit_iff hsum hp_two

/-- Value one is already maximal among all integral equations, hence proves
Mathlib's actual minimality condition. -/
theorem padicWeierstrass_isMinimal_of_discriminant_valuation_one {p : ℕ}
    [Fact p.Prime] (W : WeierstrassCurve ℚ_[p])
    [WeierstrassCurve.IsIntegral ℤ_[p] W]
    (hvaluation : freyPadicValuation p W.Δ = 1) :
    WeierstrassCurve.IsMinimal ℤ_[p] W := by
  constructor
  constructor
  · simpa only [one_smul] using
      (inferInstance : WeierstrassCurve.IsIntegral ℤ_[p] W)
  · intro C hC _
    letI : WeierstrassCurve.IsIntegral ℤ_[p] (C • W) := hC
    change (WeierstrassCurve.valuation_Δ_aux ℤ_[p] (C • W) : ℤᵐ⁰) ≤
      (WeierstrassCurve.valuation_Δ_aux ℤ_[p] ((1 : WeierstrassCurve.VariableChange ℚ_[p]) • W) : ℤᵐ⁰)
    have hbound := (WeierstrassCurve.valuation_Δ_aux ℤ_[p] (C • W)).property
    simpa only [one_smul, WeierstrassCurve.valuation_Δ_aux_eq_of_isIntegral,
      hvaluation] using hbound

/-- The specific integral ABC equation is minimal off its odd discriminant support. -/
theorem freyPadicCurve_isMinimal_of_not_dvd {p a b c : ℕ} [Fact p.Prime]
    (hsum : a + b = c) (hp_two : p ≠ 2) (hnot : ¬ p ∣ a * b * c) :
    WeierstrassCurve.IsMinimal ℤ_[p] (freyPadicCurve p a b) := by
  letI := freyPadicCurve_isIntegral p a b
  exact padicWeierstrass_isMinimal_of_discriminant_valuation_one _
    (freyPadicCurve_discriminant_valuation_eq_one hsum hp_two hnot)

/-- This is Mathlib's good-reduction predicate, including the proved minimality. -/
theorem freyPadicCurve_hasGoodReduction_of_not_dvd {p a b c : ℕ} [Fact p.Prime]
    (hsum : a + b = c) (hp_two : p ≠ 2) (hnot : ¬ p ∣ a * b * c) :
    WeierstrassCurve.HasGoodReduction ℤ_[p] (freyPadicCurve p a b) := by
  haveI := freyPadicCurve_isMinimal_of_not_dvd hsum hp_two hnot
  exact WeierstrassCurve.HasGoodReduction.mk
    (freyPadicCurve_discriminant_valuation_eq_one hsum hp_two hnot)

/-- Positive ABC inputs give an elliptic generic fibre, not a singular cubic
being classified by reduction terminology. -/
theorem freyPadicCurve_isElliptic {p a b : ℕ} [Fact p.Prime]
    (ha : 0 < a) (hb : 0 < b) :
    (freyPadicCurve p a b).IsElliptic := by
  rw [freyPadicCurve, freyWeierstrassCurve_isElliptic_iff]
  refine ⟨by norm_num, ?_, ?_, ?_⟩
  · exact Nat.cast_ne_zero.mpr (by omega)
  · exact Nat.cast_ne_zero.mpr (by omega)
  · rw [← Nat.cast_add]
    exact Nat.cast_ne_zero.mpr (by omega)

/-- The `c₄` invariant also commutes with passage to the fraction field. -/
theorem freyPadicCurve_c4_eq_map_integral (p a b : ℕ) [Fact p.Prime] :
    (freyPadicCurve p a b).c₄ =
      algebraMap ℤ_[p] ℚ_[p] (freyPadicIntegralModel p a b).c₄ := by
  rw [← freyPadicIntegralModel_baseChange p a b,
    WeierstrassCurve.baseChange, WeierstrassCurve.map_c₄]

/-- Every actual integral equation has `c₄` of valuation at most one. -/
theorem padicWeierstrass_c4_valuation_le_one {p : ℕ} [Fact p.Prime]
    (W : WeierstrassCurve ℚ_[p]) [WeierstrassCurve.IsIntegral ℤ_[p] W] :
    freyPadicValuation p W.c₄ ≤ 1 := by
  rw [← WeierstrassCurve.integralModel_c₄_eq ℤ_[p] W]
  exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one
    (IsDiscreteValuationRing.maximalIdeal ℤ_[p]) (W.integralModel ℤ_[p]).c₄

/-- The `c₄` formula uses the same natural invariant polynomial as the ABC
coprimality theorem, rather than a separately postulated invariant. -/
theorem freyPadicIntegralModel_c4 (p a b : ℕ) [Fact p.Prime] :
    (freyPadicIntegralModel p a b).c₄ =
      16 * (abcInvariantPolynomial a b : ℤ_[p]) := by
  rw [freyPadicIntegralModel, freyWeierstrassCurve_c₄]
  simp only [abcInvariantPolynomial, Nat.cast_add, Nat.cast_mul, Nat.cast_pow]

/-- The factor `16` remains a genuine `p`-adic integral unit at odd primes. -/
theorem freyPadic_sixteen_isUnit {p : ℕ} [Fact p.Prime] (hp_two : p ≠ 2) :
    IsUnit (16 : ℤ_[p]) := by
  change IsUnit ((16 : ℕ) : ℤ_[p])
  rw [freyPadic_natCast_isUnit_iff]
  intro hdiv
  have hdiv_two : p ∣ 2 := (Fact.out : p.Prime).dvd_of_dvd_pow
    (show p ∣ 2 ^ 4 by norm_num; exact hdiv)
  rcases (Nat.dvd_prime Nat.prime_two).mp hdiv_two with hone | htwo
  · exact (Fact.out : p.Prime).ne_one hone
  · exact hp_two htwo

/-- At an odd prime of `abc`, coprimality of the actual invariant polynomial
with `abc` makes the actual model's `c₄` a unit in `ℤ_[p]`. -/
theorem freyPadicIntegralModel_c4_isUnit_of_dvd {p a b c : ℕ} [Fact p.Prime]
    (h : IsABCTriple a b c) (hp_two : p ≠ 2) (hdiv : p ∣ a * b * c) :
    IsUnit (freyPadicIntegralModel p a b).c₄ := by
  have hcop := h.abcInvariantPolynomial_coprime_product
  have hnot : ¬ p ∣ abcInvariantPolynomial a b := by
    intro hpoly
    have hone : p ∣ 1 := by
      simpa only [hcop.gcd_eq_one] using Nat.dvd_gcd hpoly hdiv
    exact (Fact.out : p.Prime).ne_one (Nat.dvd_one.mp hone)
  rw [freyPadicIntegralModel_c4]
  exact (freyPadic_sixteen_isUnit hp_two).mul
    ((freyPadic_natCast_isUnit_iff p (abcInvariantPolynomial a b)).mpr hnot)

/-- The `c₄` unit gives exactly the DVR valuation required for multiplicative
reduction; minimality is established separately before using that predicate. -/
theorem freyPadicCurve_c4_valuation_eq_one_of_dvd {p a b c : ℕ} [Fact p.Prime]
    (h : IsABCTriple a b c) (hp_two : p ≠ 2) (hdiv : p ∣ a * b * c) :
    freyPadicValuation p (freyPadicCurve p a b).c₄ = 1 := by
  rw [freyPadicCurve_c4_eq_map_integral]
  exact freyPadicValuation_eq_one_of_isUnit
    (freyPadicIntegralModel_c4_isUnit_of_dvd h hp_two hdiv)

/-- The weight-twelve identity eliminates the change-of-variable scaling
factor without assuming a nonzero discriminant or dividing by `c₄`. -/
theorem freyReduction_discriminant_c4_change_identity {R : Type*} [CommRing R]
    (W : WeierstrassCurve R) (C : WeierstrassCurve.VariableChange R) :
    (C • W).Δ * W.c₄ ^ 3 = W.Δ * (C • W).c₄ ^ 3 := by
  rw [WeierstrassCurve.variableChange_Δ, WeierstrassCurve.variableChange_c₄]
  ring

/-- A unit `c₄` forces the given integral equation to be minimal: every other
integral variable change has discriminant valuation at most the original one. -/
theorem padicWeierstrass_isMinimal_of_c4_valuation_one {p : ℕ} [Fact p.Prime]
    (W : WeierstrassCurve ℚ_[p]) [WeierstrassCurve.IsIntegral ℤ_[p] W]
    (hvaluation : freyPadicValuation p W.c₄ = 1) :
    WeierstrassCurve.IsMinimal ℤ_[p] W := by
  constructor
  constructor
  · simpa only [one_smul] using
      (inferInstance : WeierstrassCurve.IsIntegral ℤ_[p] W)
  · intro C hC _
    letI : WeierstrassCurve.IsIntegral ℤ_[p] (C • W) := hC
    have hidentity := congrArg (freyPadicValuation p)
      (freyReduction_discriminant_c4_change_identity W C)
    simp only [map_mul, map_pow, hvaluation, one_pow, mul_one] at hidentity
    have hc4 := padicWeierstrass_c4_valuation_le_one (C • W)
    have hpower : (freyPadicValuation p (C • W).c₄) ^ 3 ≤ 1 := by
      simpa only [pow_succ, pow_zero, one_mul, mul_one] using
        mul_le_mul' (mul_le_mul' hc4 hc4) hc4
    have hcomparison : freyPadicValuation p (C • W).Δ ≤ freyPadicValuation p W.Δ := by
      calc
        freyPadicValuation p (C • W).Δ =
            freyPadicValuation p W.Δ * (freyPadicValuation p (C • W).c₄) ^ 3 := hidentity
        _ ≤ freyPadicValuation p W.Δ * 1 := mul_le_mul_left' hpower _
        _ = freyPadicValuation p W.Δ := mul_one _
    change (WeierstrassCurve.valuation_Δ_aux ℤ_[p] (C • W) : ℤᵐ⁰) ≤
      (WeierstrassCurve.valuation_Δ_aux ℤ_[p] ((1 : WeierstrassCurve.VariableChange ℚ_[p]) • W) : ℤᵐ⁰)
    simpa only [one_smul, WeierstrassCurve.valuation_Δ_aux_eq_of_isIntegral] using hcomparison

/-- At odd primes dividing `abc`, the unit `c₄` proves actual minimality. -/
theorem freyPadicCurve_isMinimal_of_dvd {p a b c : ℕ} [Fact p.Prime]
    (h : IsABCTriple a b c) (hp_two : p ≠ 2) (hdiv : p ∣ a * b * c) :
    WeierstrassCurve.IsMinimal ℤ_[p] (freyPadicCurve p a b) := by
  letI := freyPadicCurve_isIntegral p a b
  exact padicWeierstrass_isMinimal_of_c4_valuation_one _
    (freyPadicCurve_c4_valuation_eq_one_of_dvd h hp_two hdiv)

/-- The displayed integral Frey equation is minimal at every odd prime. -/
theorem freyPadicCurve_isMinimal {p a b c : ℕ} [Fact p.Prime]
    (h : IsABCTriple a b c) (hp_two : p ≠ 2) :
    WeierstrassCurve.IsMinimal ℤ_[p] (freyPadicCurve p a b) := by
  by_cases hdiv : p ∣ a * b * c
  · exact freyPadicCurve_isMinimal_of_dvd h hp_two hdiv
  · exact freyPadicCurve_isMinimal_of_not_dvd h.2.2.1 hp_two hdiv

/-- This is actual multiplicative reduction of the minimal `p`-adic equation,
including both its discriminant and `c₄` valuation conditions. -/
theorem freyPadicCurve_hasMultiplicativeReduction_of_dvd {p a b c : ℕ}
    [Fact p.Prime] (h : IsABCTriple a b c) (hp_two : p ≠ 2)
    (hdiv : p ∣ a * b * c) :
    WeierstrassCurve.HasMultiplicativeReduction ℤ_[p] (freyPadicCurve p a b) := by
  haveI := freyPadicCurve_isMinimal_of_dvd h hp_two hdiv
  exact WeierstrassCurve.HasMultiplicativeReduction.mk
    ((freyPadicCurve_discriminant_valuation_lt_one_iff h.2.2.1 hp_two).mpr hdiv)
    (freyPadicCurve_c4_valuation_eq_one_of_dvd h hp_two hdiv)

/-- Exact good-reduction criterion after actual odd-prime minimality is available. -/
theorem freyPadicCurve_hasGoodReduction_iff {p a b c : ℕ} [Fact p.Prime]
    (h : IsABCTriple a b c) (hp_two : p ≠ 2) :
    WeierstrassCurve.HasGoodReduction ℤ_[p] (freyPadicCurve p a b) ↔
      ¬ p ∣ a * b * c := by
  constructor
  · intro hgood hdiv
    have hbad := (freyPadicCurve_discriminant_valuation_lt_one_iff
      h.2.2.1 hp_two).mpr hdiv
    rw [hgood.goodReduction] at hbad
    exact lt_irrefl 1 hbad
  · exact freyPadicCurve_hasGoodReduction_of_not_dvd h.2.2.1 hp_two

/-- Exact multiplicative-reduction criterion at every odd prime. -/
theorem freyPadicCurve_hasMultiplicativeReduction_iff {p a b c : ℕ} [Fact p.Prime]
    (h : IsABCTriple a b c) (hp_two : p ≠ 2) :
    WeierstrassCurve.HasMultiplicativeReduction ℤ_[p] (freyPadicCurve p a b) ↔
      p ∣ a * b * c := by
  constructor
  · intro hmult
    exact (freyPadicCurve_discriminant_valuation_lt_one_iff h.2.2.1 hp_two).mp
      hmult.badReduction
  · exact freyPadicCurve_hasMultiplicativeReduction_of_dvd h hp_two

/-- The actual minimal equation has good or multiplicative reduction at every
odd prime; no conductor exponent or classification at `2` is asserted here. -/
theorem freyPadicCurve_hasGoodReduction_or_hasMultiplicativeReduction
    {p a b c : ℕ} [Fact p.Prime] (h : IsABCTriple a b c) (hp_two : p ≠ 2) :
    WeierstrassCurve.HasGoodReduction ℤ_[p] (freyPadicCurve p a b) ∨
      WeierstrassCurve.HasMultiplicativeReduction ℤ_[p] (freyPadicCurve p a b) := by
  by_cases hdiv : p ∣ a * b * c
  · exact Or.inr (freyPadicCurve_hasMultiplicativeReduction_of_dvd h hp_two hdiv)
  · exact Or.inl (freyPadicCurve_hasGoodReduction_of_not_dvd h.2.2.1 hp_two hdiv)

/-- Actual additive reduction is ruled out for this minimal equation at odd primes. -/
theorem freyPadicCurve_not_hasAdditiveReduction {p a b c : ℕ} [Fact p.Prime]
    (h : IsABCTriple a b c) (hp_two : p ≠ 2) :
    ¬ WeierstrassCurve.HasAdditiveReduction ℤ_[p] (freyPadicCurve p a b) := by
  rcases freyPadicCurve_hasGoodReduction_or_hasMultiplicativeReduction h hp_two with
    hgood | hmult
  · exact hgood.not_hasAdditiveReduction
  · exact hmult.not_hasAdditiveReduction

/-- The minimal residue curve in Mathlib is elliptic exactly off `abc`.  Its
minimality instance is supplied by the actual proof above, not assumed. -/
theorem freyPadicCurve_reduction_isElliptic_iff {p a b c : ℕ} [Fact p.Prime]
    (h : IsABCTriple a b c) (hp_two : p ≠ 2) :
    letI : WeierstrassCurve.IsMinimal ℤ_[p] (freyPadicCurve p a b) :=
      freyPadicCurve_isMinimal h hp_two
    ((freyPadicCurve p a b).reduction ℤ_[p]).IsElliptic ↔ ¬ p ∣ a * b * c := by
  letI : WeierstrassCurve.IsMinimal ℤ_[p] (freyPadicCurve p a b) :=
    freyPadicCurve_isMinimal h hp_two
  exact (WeierstrassCurve.hasGoodReduction_iff_isElliptic_reduction
    (R := ℤ_[p]) (W := freyPadicCurve p a b)).symm.trans
      (freyPadicCurve_hasGoodReduction_iff h hp_two)

end LeanFormal.IUT
