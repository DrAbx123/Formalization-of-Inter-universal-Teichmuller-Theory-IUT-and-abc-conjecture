import LeanFormal.IUT.ABCBridge.Geometry.FreyOddReduction
import LeanFormal.IUT.ABCBridge.Arithmetic.ABCInvariantLocalValuations

/-!
# The Frey curve at the prime `2`: 2-adic valuations and the reduction gap

This file isolates what is proved in this repository today about the actual
ABC Frey equation `y * y = x * (x - a) * (x + b)` at the prime `2`, and
states the remaining 2-adic conductor gap explicitly.  It mirrors the odd
part file `FreyConductorOdd` at the level of definitions.

## Proved

* `padicValNat_two_sixteen_mul_square`: for `t ≠ 0`,
  `v₂(16 * t ^ 2) = 4 + 2 * v₂(t)`; the factor `16 = 2 ^ 4` contributes `4`
  and the square doubles the valuation of `t`.  On actual ABC triples,
  `IsABCTriple.padicValNat_two_freyDiscriminant` reads
  `v₂(16 * a ^ 2 * b ^ 2 * c ^ 2) = 4 + 2 * v₂(a * b * c)`.
* `IsABCTriple.padicValNat_two_sixteen_abcInvariantPolynomial`: the `c₄`
  coefficient `16 * (a ^ 2 + a * b + b ^ 2)` has exact 2-adic valuation `4`.
* `freyPadicIntegralModel_two_c4_eq_natCast`,
  `freyPadicIntegralModel_two_discriminant_eq_natCast`: the actual formulas
  for `c₄` and `Δ` of the displayed integral model at `2` as casts of
  natural numbers, for every `a b : ℕ`, with no ABC hypothesis.
* `freyPadicIntegralModel_two_c4_not_isUnit`,
  `freyPadicIntegralModel_two_discriminant_not_isUnit`, and their generic
  fibre forms `freyPadicCurve_two_c4_valuation_lt_one`,
  `freyPadicCurve_two_discriminant_valuation_lt_one`: at `2` both `c₄` and
  `Δ` of the displayed model are non-units, hence have DVR valuation `< 1`.
  This holds for *every* parameter pair `(a, b)`.
* `freyPadicCurve_two_not_hasGoodReduction`,
  `freyPadicCurve_two_not_hasMultiplicativeReduction`: the displayed model
  `freyPadicCurve 2 a b` has neither good nor multiplicative reduction at
  `2` (good reduction is refuted through `Δ`, multiplicative through `c₄`).
* `freyPadicCurve_two_hasAdditiveReduction_of_isMinimal` and the exact
  criterion `freyPadicCurve_two_hasAdditiveReduction_iff_isMinimal`: the
  displayed model has additive reduction at `2` **if and only if** it is
  minimal at `2`.  Minimality at `2` is the missing premise and is not
  proved in this file.
* `conductorExponentTwoAdic` with three branch lemmas, mirroring
  `conductorExponentOdd` of `FreyConductorOdd`.

## Not proved / not claimed

* **No minimality at `2`.** Mathlib's `HasGoodReduction` /
  `HasMultiplicativeReduction` / `HasAdditiveReduction` extend
  `IsMinimal R W` and refer to the *given* model.  No minimality of the
  displayed model at `2` (nor of any explicit 2-adic variable change of it)
  is proved here, so nothing below identifies an arithmetic conductor
  exponent at `2`.
* **No conductor exponent, no Tate correction.** The local invariants
  needed for the exponent at `2` (Tate algorithm at `p = 2`, Ogg–Saito
  exponents, component counts `m_p`, wild ramification) are not available
  in Mathlib or in this repository; the formula
  `ord_p(Δ) = ord_p(N_E) + correction` is neither stated nor used nor
  claimed.  `conductorExponentTwoAdic` is a function of the given model and
  agrees with the arithmetic conductor exponent only for minimal models.
* **Placeholder branch.** The third branch of `conductorExponentTwoAdic`
  (neither good nor multiplicative reduction) returns the constant `2`.
  This is a placeholder in the same sense as in `FreyConductorOdd`: a
  definitional value, not an additive-conductor claim.  The only
  declarations consuming it are the definitional unfoldings
  `conductorExponentTwoAdic_eq_two_of_not_hasGoodReduction_not_hasMultiplicativeReduction`
  and `freyPadicCurve_two_conductorExponentTwoAdic_eq_two`; the latter
  records that the placeholder evaluates to `2` on the displayed Frey model,
  and this value is not consumed by any conductor, support, or height
  statement.
* The odd-prime theory (good / multiplicative classification, minimality of
  the displayed model, identification of the odd conductor part) lives in
  `FreyOddReduction` and `FreyConductorOdd` and is not repeated here.
-/

noncomputable section

open scoped WeierstrassCurve

namespace LeanFormal.IUT

/-! ## The local 2-adic conductor exponent -/

/-- The conductor exponent at the prime `2` of a Weierstrass model over
`ℚ_[2]`, read off from its reduction type: `0` for good reduction, `1` for
multiplicative reduction, and the placeholder value `2` otherwise.

Only the first two branches carry mathematical content in this file; the
third branch is not a claim about additive reduction, whose arithmetic
exponent depends on Ogg–Saito data not available here. -/
noncomputable def conductorExponentTwoAdic (E : WeierstrassCurve ℚ_[2]) : ℕ := by
  classical
  exact
    if WeierstrassCurve.HasGoodReduction ℤ_[2] E then 0
    else if WeierstrassCurve.HasMultiplicativeReduction ℤ_[2] E then 1
    else 2

/-- Good reduction of the given model at `2` contributes local exponent
zero. -/
theorem conductorExponentTwoAdic_eq_zero_of_hasGoodReduction
    {E : WeierstrassCurve ℚ_[2]}
    (h : WeierstrassCurve.HasGoodReduction ℤ_[2] E) :
    conductorExponentTwoAdic E = 0 := by
  classical
  rw [conductorExponentTwoAdic]
  exact if_pos h

/-- Multiplicative reduction of the given model at `2` contributes local
exponent one.  The mutual exclusivity of good and multiplicative reduction
is Mathlib's `HasMultiplicativeReduction.not_hasGoodReduction`. -/
theorem conductorExponentTwoAdic_eq_one_of_hasMultiplicativeReduction
    {E : WeierstrassCurve ℚ_[2]}
    (h : WeierstrassCurve.HasMultiplicativeReduction ℤ_[2] E) :
    conductorExponentTwoAdic E = 1 := by
  classical
  rw [conductorExponentTwoAdic]
  rw [if_neg h.not_hasGoodReduction, if_pos h]

/-- The placeholder branch: if the given model has neither good nor
multiplicative reduction, the definition returns the constant `2`.  This is
a pure definitional unfolding; it is not a claim that the arithmetic
conductor exponent at `2` is `2`. -/
theorem conductorExponentTwoAdic_eq_two_of_not_hasGoodReduction_not_hasMultiplicativeReduction
    {E : WeierstrassCurve ℚ_[2]}
    (hgood : ¬ WeierstrassCurve.HasGoodReduction ℤ_[2] E)
    (hmult : ¬ WeierstrassCurve.HasMultiplicativeReduction ℤ_[2] E) :
    conductorExponentTwoAdic E = 2 := by
  classical
  rw [conductorExponentTwoAdic, if_neg hgood, if_neg hmult]

/-! ## The 2-adic valuation of `16 * t ^ 2` -/

/-- The factor `16 = 2 ^ 4` contributes exactly `4` to the 2-adic valuation
and the square doubles the remaining one: `v₂(16 * t ^ 2) = 4 + 2 * v₂(t)`
for `t ≠ 0`. -/
theorem padicValNat_two_sixteen_mul_square (t : ℕ) (ht : t ≠ 0) :
    padicValNat 2 (16 * t ^ 2) = 4 + 2 * padicValNat 2 t := by
  have h16 : (16 : ℕ) = 2 ^ 4 := by norm_num
  rw [h16,
    padicValNat.mul (p := 2) (a := 2 ^ 4) (b := t ^ 2) (by norm_num)
      (pow_ne_zero 2 ht)]
  simp only [padicValNat.pow, padicValNat_self, mul_one]

/-! ## The 2-adic valuations attached to an ABC triple -/

/-- On an actual ABC triple, the natural number `16 * a ^ 2 * b ^ 2 * c ^ 2`
(the discriminant of the Frey curve, in the shape displayed by
`freyWeierstrassCurve_discriminant_of_add_eq`) has 2-adic valuation
`4 + 2 * v₂(a * b * c)`. -/
theorem IsABCTriple.padicValNat_two_freyDiscriminant {a b c : ℕ}
    (h : IsABCTriple a b c) :
    padicValNat 2 (16 * a ^ 2 * b ^ 2 * c ^ 2) =
      4 + 2 * padicValNat 2 (a * b * c) := by
  have hne : a * b * c ≠ 0 := Nat.ne_of_gt h.abcInvariant_product_pos
  have hshape : 16 * a ^ 2 * b ^ 2 * c ^ 2 = 16 * (a * b * c) ^ 2 := by
    ring
  rw [hshape, padicValNat_two_sixteen_mul_square (a * b * c) hne]

/-- The `c₄` coefficient `16 * (a ^ 2 + a * b + b ^ 2)` of the displayed
Frey equation has exact 2-adic valuation `4`: the invariant polynomial
`a ^ 2 + a * b + b ^ 2` is odd on ABC triples, so only the factor `16`
contributes. -/
theorem IsABCTriple.padicValNat_two_sixteen_abcInvariantPolynomial {a b c : ℕ}
    (h : IsABCTriple a b c) :
    padicValNat 2 (16 * abcInvariantPolynomial a b) = 4 := by
  have hpoly : abcInvariantPolynomial a b ≠ 0 :=
    Nat.ne_of_gt h.abcInvariantPolynomial_pos
  have h16 : (16 : ℕ) = 2 ^ 4 := by norm_num
  rw [h16,
    padicValNat.mul (p := 2) (a := 2 ^ 4) (b := abcInvariantPolynomial a b)
      (by norm_num) hpoly]
  simp only [padicValNat.pow, padicValNat_self, mul_one,
    h.abcInvariantPolynomial_padicValNat_two]

/-! ## The displayed model at `2`: `c₄` and `Δ` as casts of natural numbers -/

/-- The `c₄` invariant of the displayed integral Frey model at `2` is the
cast of the actual natural number `16 * (a ^ 2 + a * b + b ^ 2)`.  Unlike
the odd-prime statement, no hypothesis is needed and the factor `16` stays
inside the natural-number cast, exposing it to 2-adic valuation
arithmetic. -/
theorem freyPadicIntegralModel_two_c4_eq_natCast (a b : ℕ) :
    (freyPadicIntegralModel 2 a b).c₄ =
      ((16 * abcInvariantPolynomial a b : ℕ) : ℤ_[2]) := by
  rw [freyPadicIntegralModel_c4]
  push_cast
  ring

/-- The discriminant of the displayed integral Frey model at `2` is the cast
of the actual natural number `16 * a ^ 2 * b ^ 2 * (a + b) ^ 2` (the
specialization of `freyWeierstrassCurve_discriminant` to `ℤ_[2]`), with no
hypothesis on `a b`. -/
theorem freyPadicIntegralModel_two_discriminant_eq_natCast (a b : ℕ) :
    (freyPadicIntegralModel 2 a b).Δ =
      ((16 * a ^ 2 * b ^ 2 * (a + b) ^ 2 : ℕ) : ℤ_[2]) := by
  simp only [freyPadicIntegralModel, freyWeierstrassCurve_discriminant]
  push_cast
  ring

/-! ## Non-unitness of `c₄` and `Δ` at `2` -/

/-- At `2`, the displayed integral model's `c₄` is not a unit of `ℤ_[2]`:
it is divisible by `16`. -/
theorem freyPadicIntegralModel_two_c4_not_isUnit (a b : ℕ) :
    ¬ IsUnit (freyPadicIntegralModel 2 a b).c₄ := by
  rw [freyPadicIntegralModel_two_c4_eq_natCast]
  intro hunit
  exact ((freyPadic_natCast_isUnit_iff 2 (16 * abcInvariantPolynomial a b)).mp
      hunit)
    (dvd_mul_of_dvd_left (by norm_num : (2 : ℕ) ∣ 16)
      (abcInvariantPolynomial a b))

/-- At `2`, the displayed integral model's discriminant is not a unit of
`ℤ_[2]`: it is divisible by `16`.  No hypothesis on `a b` is needed. -/
theorem freyPadicIntegralModel_two_discriminant_not_isUnit (a b : ℕ) :
    ¬ IsUnit (freyPadicIntegralModel 2 a b).Δ := by
  rw [freyPadicIntegralModel_two_discriminant_eq_natCast]
  intro hunit
  have h2 : 2 ∣ 16 * a ^ 2 * b ^ 2 * (a + b) ^ 2 :=
    ⟨8 * a ^ 2 * b ^ 2 * (a + b) ^ 2, by ring⟩
  exact ((freyPadic_natCast_isUnit_iff 2
      (16 * a ^ 2 * b ^ 2 * (a + b) ^ 2)).mp hunit) h2

/-- The generic fibre's `c₄` at `2` has DVR valuation strictly below one,
for every `(a, b)`. -/
theorem freyPadicCurve_two_c4_valuation_lt_one (a b : ℕ) :
    freyPadicValuation 2 (freyPadicCurve 2 a b).c₄ < 1 := by
  rw [freyPadicCurve_c4_eq_map_integral,
    freyPadicValuation_lt_one_iff_not_isUnit]
  exact freyPadicIntegralModel_two_c4_not_isUnit a b

/-- The generic fibre's discriminant at `2` has DVR valuation strictly below
one, for every `(a, b)`. -/
theorem freyPadicCurve_two_discriminant_valuation_lt_one (a b : ℕ) :
    freyPadicValuation 2 (freyPadicCurve 2 a b).Δ < 1 := by
  rw [freyPadicCurve_discriminant_eq_map_integral,
    freyPadicValuation_lt_one_iff_not_isUnit]
  exact freyPadicIntegralModel_two_discriminant_not_isUnit a b

/-! ## Reduction type of the displayed Frey model at `2` -/

/-- The displayed Frey model has no good reduction at `2`: its discriminant
is not a unit, for every `(a, b)`. -/
theorem freyPadicCurve_two_not_hasGoodReduction (a b : ℕ) :
    ¬ WeierstrassCurve.HasGoodReduction ℤ_[2] (freyPadicCurve 2 a b) := by
  intro hgood
  have hlt := freyPadicCurve_two_discriminant_valuation_lt_one a b
  rw [hgood.goodReduction] at hlt
  exact lt_irrefl 1 hlt

/-- The displayed Frey model has no multiplicative reduction at `2`: its
`c₄` is not a unit, for every `(a, b)`. -/
theorem freyPadicCurve_two_not_hasMultiplicativeReduction (a b : ℕ) :
    ¬ WeierstrassCurve.HasMultiplicativeReduction ℤ_[2]
      (freyPadicCurve 2 a b) := by
  intro hmult
  have hlt := freyPadicCurve_two_c4_valuation_lt_one a b
  rw [hmult.multiplicativeReduction] at hlt
  exact lt_irrefl 1 hlt

/-- The displayed Frey model has additive reduction at `2` as soon as it is
minimal at `2`.  Minimality is the missing premise: no minimality at `2` is
proved in this file. -/
theorem freyPadicCurve_two_hasAdditiveReduction_of_isMinimal (a b : ℕ)
    [hmin : WeierstrassCurve.IsMinimal ℤ_[2] (freyPadicCurve 2 a b)] :
    WeierstrassCurve.HasAdditiveReduction ℤ_[2] (freyPadicCurve 2 a b) :=
  WeierstrassCurve.HasAdditiveReduction.mk
    (freyPadicCurve_two_discriminant_valuation_lt_one a b)
    (freyPadicCurve_two_c4_valuation_lt_one a b)

/-- Exact additive-reduction criterion for the displayed Frey model at `2`:
it has additive reduction at `2` if and only if it is minimal at `2`.  The
backward direction is `freyPadicCurve_two_hasAdditiveReduction_of_isMinimal`;
the forward direction only unfolds the class extension. -/
theorem freyPadicCurve_two_hasAdditiveReduction_iff_isMinimal (a b : ℕ) :
    WeierstrassCurve.HasAdditiveReduction ℤ_[2] (freyPadicCurve 2 a b) ↔
      WeierstrassCurve.IsMinimal ℤ_[2] (freyPadicCurve 2 a b) :=
  ⟨fun h => h.toIsMinimal,
    fun h => by
      haveI := h
      exact freyPadicCurve_two_hasAdditiveReduction_of_isMinimal a b⟩

/-- The placeholder branch evaluated on the displayed Frey model: since the
model has neither good nor multiplicative reduction at `2` for every
`(a, b)`, `conductorExponentTwoAdic` returns `2` on it.  This is a
definitional unfolding of the placeholder; it is not a conductor statement
and is not consumed by any conductor, support, or height theorem. -/
theorem freyPadicCurve_two_conductorExponentTwoAdic_eq_two (a b : ℕ) :
    conductorExponentTwoAdic (freyPadicCurve 2 a b) = 2 :=
  conductorExponentTwoAdic_eq_two_of_not_hasGoodReduction_not_hasMultiplicativeReduction
    (freyPadicCurve_two_not_hasGoodReduction a b)
    (freyPadicCurve_two_not_hasMultiplicativeReduction a b)

end LeanFormal.IUT
