/-
# 2-adic minimal models of the ABC Frey equation: the halving change

The ABC Frey equation `y * y = x * (x - a) * (x + b)` over `ℚ_[2]` has
discriminant `16 * (a * b * c) ^ 2` and is therefore never 2-adically
minimal as displayed.  This file formalises the explicit half-model of the
first Tate minimalisation step at `2`, i.e. the variable change
`(x, y) ↦ (4 * x, 8 * y + x)`, Mathlib variables `u = 2, s = 1`, and
proves:

* the five coefficient formulas and the discriminant formula of the
  half-model (the discriminant drops by the exact factor `2¹² = 4096`);
* the integrality criterion: if `b = a + 1 + 4 * m` (as integers) and
  `a * b = 16 * n`, the half-model is given by the explicit integral model
  `(1, m, 0, -n, 0)` over `ℤ_[2]`;
* for the family `b = a + 1 + 4 * m`, `a * b = 16 * n` (which contains the
  case A and case B parity shapes of the ABC Frey family, one of `a`, `b`
  even, the other odd), the half-model is the minimal model at `2` and:
  - `n` odd  (i.e. `v₂(a * b * c) = 4`):  good reduction at `2`;
  - `n` even (i.e. `v₂(a * b * c) ≥ 5`): multiplicative reduction at `2`;
* the fully evaluated instance `(a, b) = (3, 16)`: `Δ = 3249 = 57²`, the
  half-model is minimal with good reduction at `2`.

Minimality of the half-model is obtained from the existing reusable
criteria `padicWeierstrass_isMinimal_of_discriminant_valuation_one` (unit
discriminant, complete) and `padicWeierstrass_isMinimal_of_c4_valuation_one`
(unit `c₄`, complete) of `FreyOddReduction`; no new minimality criterion is
needed.  The propositions formalised here are the `p = 2` rows of the
minimal-model table computed in
`tmp/dsh-2adic-minimal-model-20261016/REPORT.md` §3.2.  The displayed-model
statements of `FreyConductorTwoAdic` (non-good, non-multiplicative, additive
iff minimal) concern the *displayed*, that is non-minimal, model and are
consistent with the results here.

Not formalised in this file (precise cards at the end): the minimality of
the *displayed* model in the non-solvable cases, the split/non-split
refinement of the multiplicative reduction, the full Tate algorithm at
`p = 2`, and Kodaira label uniqueness (absent from Mathlib; see REPORT §5).
-/

import LeanFormal.IUT.ABCBridge.Geometry.FreyConductorTwoAdic

noncomputable section

open scoped WeierstrassCurve

namespace LeanFormal.IUT

/-! ## The halving change and the halved model -/

/-- The variable change `(x, y) ↦ (4 * x, 8 * y + x)`, i.e. Mathlib's
`VariableChange ⟨2, 0, 1, 0⟩`: the first step of the Tate minimalisation of
the 2-adically non-minimal ABC Frey model. -/
def freyTwoAdicHalvingChange : WeierstrassCurve.VariableChange ℚ_[2] :=
  ⟨Units.mk0 (2 : ℚ_[2]) (by norm_num), 0, 1, 0⟩

@[simp] theorem freyTwoAdicHalvingChange_u :
    ((freyTwoAdicHalvingChange.u : ℚ_[2])) = 2 := rfl

@[simp] theorem freyTwoAdicHalvingChange_r : freyTwoAdicHalvingChange.r = 0 := rfl

@[simp] theorem freyTwoAdicHalvingChange_s : freyTwoAdicHalvingChange.s = 1 := rfl

@[simp] theorem freyTwoAdicHalvingChange_t : freyTwoAdicHalvingChange.t = 0 := rfl

/-- The half-model `(x, y) ↦ (4 * x, 8 * y + x)` of the actual ABC Frey
equation over `ℚ_[2]`. -/
def freyTwoAdicHalvingModel (a b : ℕ) : WeierstrassCurve ℚ_[2] :=
  freyTwoAdicHalvingChange • freyPadicCurve 2 a b

/-! ## Coefficient and invariant formulas

The halved model is `y² + y = x³ + ((b - a - 1)/4) x² - (ab/16) x`, integral
exactly under the congruences of the next section. -/

/-- The halved model has `a₁ = 1`, hence `c₄ ≡ a₁⁴ ≡ 1 (mod 2)`: the node
condition of the multiplicative-reduction template is available. -/
theorem freyTwoAdicHalvingModel_a₁ (a b : ℕ) :
    (freyTwoAdicHalvingModel a b).a₁ = 1 := by
  rw [freyTwoAdicHalvingModel, WeierstrassCurve.variableChange_a₁]
  simp [freyTwoAdicHalvingChange, freyPadicCurve]

/-- The halved model has `a₂ = (b - a - 1) / 4`. -/
theorem freyTwoAdicHalvingModel_a₂ (a b : ℕ) :
    (freyTwoAdicHalvingModel a b).a₂ =
      ((b : ℚ_[2]) - a - 1) / 4 := by
  rw [freyTwoAdicHalvingModel, WeierstrassCurve.variableChange_a₂]
  simp [freyTwoAdicHalvingChange, freyPadicCurve]
  ring

/-- The halved model has `a₃ = 0`. -/
theorem freyTwoAdicHalvingModel_a₃ (a b : ℕ) :
    (freyTwoAdicHalvingModel a b).a₃ = 0 := by
  rw [freyTwoAdicHalvingModel, WeierstrassCurve.variableChange_a₃]
  simp [freyTwoAdicHalvingChange, freyPadicCurve]

/-- The halved model has `a₄ = - (a * b) / 16`. -/
theorem freyTwoAdicHalvingModel_a₄ (a b : ℕ) :
    (freyTwoAdicHalvingModel a b).a₄ = -((a : ℚ_[2]) * b) / 16 := by
  rw [freyTwoAdicHalvingModel, WeierstrassCurve.variableChange_a₄]
  simp [freyTwoAdicHalvingChange, freyPadicCurve]
  ring

/-- The halved model has `a₆ = 0`. -/
theorem freyTwoAdicHalvingModel_a₆ (a b : ℕ) :
    (freyTwoAdicHalvingModel a b).a₆ = 0 := by
  rw [freyTwoAdicHalvingModel, WeierstrassCurve.variableChange_a₆]
  simp [freyTwoAdicHalvingChange, freyPadicCurve]

/-- The discriminant of the halved model: the factor `u⁻¹² = 2⁻¹² = 1/4096`
is exact. -/
theorem freyTwoAdicHalvingModel_discriminant {a b c : ℕ} (hsum : a + b = c) :
    (freyTwoAdicHalvingModel a b).Δ =
      (16 * (a * b * c) ^ 2 : ℚ_[2]) / 4096 := by
  rw [freyTwoAdicHalvingModel, WeierstrassCurve.variableChange_Δ,
    freyPadicCurve_discriminant hsum]
  simp [freyTwoAdicHalvingChange]
  ring_nf

/-- The invariant `c₄` of the halved model is the actual integer
`abcInvariantPolynomial a b = a² + ab + b²` (the factor `16 = u⁴` cancels). -/
theorem freyTwoAdicHalvingModel_c₄ (a b : ℕ) :
    (freyTwoAdicHalvingModel a b).c₄ = ((abcInvariantPolynomial a b : ℕ) : ℚ_[2]) := by
  rw [freyTwoAdicHalvingModel, WeierstrassCurve.variableChange_c₄,
    freyPadicCurve_c4_eq_map_integral, freyPadicIntegralModel_two_c4_eq_natCast]
  simp only [abcInvariantPolynomial, map_natCast]
  simp [freyTwoAdicHalvingChange]
  ring_nf

/-- Congruence form of the discriminant: under `a * b = 16 * n` the
discriminant is the perfect square `(n * (a + b))²`. -/
theorem freyTwoAdicHalvingModel_discriminant_of_congruences {a b n : ℕ}
    (hab : a * b = 16 * n) :
    (freyTwoAdicHalvingModel a b).Δ = (((n * (a + b)) ^ 2 : ℕ) : ℚ_[2]) := by
  rw [freyTwoAdicHalvingModel_discriminant (show a + b = a + b from rfl)]
  have hab' : (a : ℚ_[2]) * b = 16 * (n : ℚ_[2]) := by
    have h := congrArg (fun z : ℕ => (z : ℚ_[2])) hab
    push_cast at h
    exact h
  rw [hab']
  push_cast
  ring_nf

/-! ## 2-adic valuation of integer casts -/

/-- For the DVR valuation at `2`, an integer cast is a unit (value `1`)
exactly when `2` does not divide it. -/
theorem freyPadicValuation_two_natCast_eq_one_iff (n : ℕ) :
    freyPadicValuation 2 (n : ℚ_[2]) = 1 ↔ ¬ 2 ∣ n := by
  have hcast : (n : ℚ_[2]) = algebraMap ℤ_[2] ℚ_[2] (n : ℤ_[2]) :=
    (map_natCast (algebraMap ℤ_[2] ℚ_[2]) n).symm
  constructor
  · intro h
    rw [← freyPadic_natCast_isUnit_iff 2 n]
    by_contra hnu
    have hlt : freyPadicValuation 2 (n : ℚ_[2]) < 1 := by
      rw [hcast, freyPadicValuation_lt_one_iff_not_isUnit]
      exact hnu
    rw [h] at hlt
    exact lt_irrefl 1 hlt
  · intro h
    rw [hcast]
    exact freyPadicValuation_eq_one_of_isUnit ((freyPadic_natCast_isUnit_iff 2 n).mpr h)

/-- For the DVR valuation at `2`, an integer cast has value `< 1` (is not a
unit) exactly when `2` divides it. -/
theorem freyPadicValuation_two_natCast_lt_one_iff (n : ℕ) :
    freyPadicValuation 2 (n : ℚ_[2]) < 1 ↔ 2 ∣ n := by
  have hcast : (n : ℚ_[2]) = algebraMap ℤ_[2] ℚ_[2] (n : ℤ_[2]) :=
    (map_natCast (algebraMap ℤ_[2] ℚ_[2]) n).symm
  rw [hcast, freyPadicValuation_lt_one_iff_not_isUnit, freyPadic_natCast_isUnit_iff]
  exact not_not

/-! ## Integrality of the halved model from congruences -/

/-- If `b = a + 1 + 4 * m` (as integers) and `a * b = 16 * n`, the halved
Frey model is integral at `2`, with the explicit integral model
`(1, m, 0, -n, 0)` over `ℤ_[2]`. -/
theorem freyTwoAdicHalvingModel_isIntegral_of_congruences {a b : ℕ} {m : ℤ} {n : ℕ}
    (hb : (b : ℤ) = (a : ℤ) + 1 + 4 * m) (hab : a * b = 16 * n) :
    WeierstrassCurve.IsIntegral ℤ_[2] (freyTwoAdicHalvingModel a b) := by
  refine ⟨⟨⟨1, (m : ℤ_[2]), 0, -(n : ℤ_[2]), 0⟩, ?_⟩⟩
  rw [WeierstrassCurve.baseChange]
  have hb' : (b : ℚ_[2]) = (a : ℚ_[2]) + 1 + 4 * (m : ℚ_[2]) := by
    have h := congrArg (fun z : ℤ => (z : ℚ_[2])) hb
    push_cast at h
    exact h
  have hab' : (a : ℚ_[2]) * b = 16 * (n : ℚ_[2]) := by
    have h := congrArg (fun z : ℕ => (z : ℚ_[2])) hab
    push_cast at h
    exact h
  ext
  · simp [WeierstrassCurve.map_a₁, WeierstrassCurve.variableChange_a₁,
      freyTwoAdicHalvingModel, freyTwoAdicHalvingChange, freyPadicCurve]
  · simp [WeierstrassCurve.map_a₂, WeierstrassCurve.variableChange_a₂,
      freyTwoAdicHalvingModel, freyTwoAdicHalvingChange, freyPadicCurve, hb']
    ring
  · simp [WeierstrassCurve.map_a₃, WeierstrassCurve.variableChange_a₃,
      freyTwoAdicHalvingModel, freyTwoAdicHalvingChange, freyPadicCurve]
  · simp [WeierstrassCurve.map_a₄, WeierstrassCurve.variableChange_a₄,
      freyTwoAdicHalvingModel, freyTwoAdicHalvingChange, freyPadicCurve, hab']
    ring
  · simp [WeierstrassCurve.map_a₆, WeierstrassCurve.variableChange_a₆,
      freyTwoAdicHalvingModel, freyTwoAdicHalvingChange, freyPadicCurve]

/-! ## Parity from the congruence `b = a + 1 + 4 * m` -/

/-- `b = a + 1 + 4 * m` makes `a + b` odd; equivalently exactly one of `a`,
`b` is even, so the family covers both the case A and the case B parity
shapes of the ABC Frey triples. -/
theorem odd_add_of_int_congruence {a b : ℕ} {m : ℤ}
    (hb : (b : ℤ) = (a : ℤ) + 1 + 4 * m) : Odd (a + b) := by
  have hZ : Odd (((a + b : ℕ)) : ℤ) := by
    refine ⟨(a : ℤ) + 2 * m, ?_⟩
    push_cast
    rw [hb]
    ring
  exact (Int.odd_coe_nat _).mp hZ

/-- `b = a + 1 + 4 * m` makes the invariant `a² + a * b + b²` odd, hence a
2-adic unit; this is the `c₄` unit input of
`padicWeierstrass_isMinimal_of_c4_valuation_one`. -/
theorem odd_abcInvariantPolynomial_of_int_congruence {a b : ℕ} {m : ℤ}
    (hb : (b : ℤ) = (a : ℤ) + 1 + 4 * m) : Odd (abcInvariantPolynomial a b) := by
  have hZ : Odd ((abcInvariantPolynomial a b : ℕ) : ℤ) := by
    have hdecomp : ((abcInvariantPolynomial a b : ℕ) : ℤ)
        = 3 * ((a : ℤ) * ((a : ℤ) + 1)) + 4 * (m * (3 * (a : ℤ) + 2 + 4 * m)) + 1 := by
      rw [abcInvariantPolynomial]
      push_cast
      rw [hb]
      ring
    rw [hdecomp]
    obtain ⟨t, ht⟩ := Int.two_dvd_mul_add_one (a : ℤ)
    refine ⟨3 * t + 2 * (m * (3 * (a : ℤ) + 2 + 4 * m)), ?_⟩
    rw [ht]
    ring
  exact (Int.odd_coe_nat _).mp hZ

/-- An odd natural number is not divisible by `2`. -/
theorem two_not_dvd_of_odd {n : ℕ} (hn : Odd n) : ¬ 2 ∣ n :=
  fun h => (Nat.not_even_iff_odd.mpr hn) (even_iff_two_dvd.mpr h)

/-! ## The main reduction-type theorems for the solvable family

Under `b = a + 1 + 4 * m` and `a * b = 16 * n` the halved model is the
minimal model at `2`, and the reduction type is decided by the parity of
`n = v₂(a * b) - 4`.  Minimality comes from the existing criteria
`padicWeierstrass_isMinimal_of_discriminant_valuation_one` (good case,
unit discriminant `(n * (a + b))²`) and
`padicWeierstrass_isMinimal_of_c4_valuation_one` (multiplicative case, unit
`c₄ = abcInvariantPolynomial a b`). -/

/-- **Good reduction at `2`** for the solvable family with `n` odd, i.e.
`v₂(a * b * c) = 4`. -/
theorem freyTwoAdicHalvingModel_hasGoodReduction_of_congruences {a b : ℕ} {m : ℤ} {n : ℕ}
    (hb : (b : ℤ) = (a : ℤ) + 1 + 4 * m) (hab : a * b = 16 * n) (hn : Odd n) :
    WeierstrassCurve.HasGoodReduction ℤ_[2] (freyTwoAdicHalvingModel a b) := by
  haveI hint : WeierstrassCurve.IsIntegral ℤ_[2] (freyTwoAdicHalvingModel a b) :=
    freyTwoAdicHalvingModel_isIntegral_of_congruences hb hab
  have hnc_odd : Odd (n * (a + b)) := hn.mul (odd_add_of_int_congruence hb)
  have hval : freyPadicValuation 2 (freyTwoAdicHalvingModel a b).Δ = 1 := by
    rw [freyTwoAdicHalvingModel_discriminant_of_congruences hab]
    exact (freyPadicValuation_two_natCast_eq_one_iff _).mpr
      (two_not_dvd_of_odd (Odd.pow (n := 2) hnc_odd))
  haveI hmin : WeierstrassCurve.IsMinimal ℤ_[2] (freyTwoAdicHalvingModel a b) :=
    padicWeierstrass_isMinimal_of_discriminant_valuation_one _ hval
  exact WeierstrassCurve.HasGoodReduction.mk hval

/-- **Multiplicative reduction at `2`** for the solvable family with `n`
even, i.e. `v₂(a * b * c) ≥ 5`. -/
theorem freyTwoAdicHalvingModel_hasMultiplicativeReduction_of_congruences {a b : ℕ} {m : ℤ}
    {n : ℕ} (hb : (b : ℤ) = (a : ℤ) + 1 + 4 * m) (hab : a * b = 16 * n) (hn : 2 ∣ n) :
    WeierstrassCurve.HasMultiplicativeReduction ℤ_[2] (freyTwoAdicHalvingModel a b) := by
  haveI hint : WeierstrassCurve.IsIntegral ℤ_[2] (freyTwoAdicHalvingModel a b) :=
    freyTwoAdicHalvingModel_isIntegral_of_congruences hb hab
  have hc4 : freyPadicValuation 2 (freyTwoAdicHalvingModel a b).c₄ = 1 := by
    rw [freyTwoAdicHalvingModel_c₄]
    exact (freyPadicValuation_two_natCast_eq_one_iff _).mpr
      (two_not_dvd_of_odd (odd_abcInvariantPolynomial_of_int_congruence hb))
  haveI hmin : WeierstrassCurve.IsMinimal ℤ_[2] (freyTwoAdicHalvingModel a b) :=
    padicWeierstrass_isMinimal_of_c4_valuation_one _ hc4
  refine WeierstrassCurve.HasMultiplicativeReduction.mk ?_ hc4
  rw [freyTwoAdicHalvingModel_discriminant_of_congruences hab]
  refine (freyPadicValuation_two_natCast_lt_one_iff _).mpr ?_
  obtain ⟨k, hk⟩ := hn
  refine ⟨2 * k ^ 2 * (a + b) ^ 2, ?_⟩
  rw [hk]
  ring

/-! ## The evaluated instance `(a, b) = (3, 16)` -/

theorem freyTwoAdicHalvingModel_three_sixteen_isIntegral :
    WeierstrassCurve.IsIntegral ℤ_[2] (freyTwoAdicHalvingModel 3 16) :=
  freyTwoAdicHalvingModel_isIntegral_of_congruences (m := 3) (n := 3)
    (by norm_num) (by norm_num)

/-- `Δ = 3249 = 57²` for the halved `(3, 16)` model. -/
theorem freyTwoAdicHalvingModel_three_sixteen_discriminant :
    (freyTwoAdicHalvingModel 3 16).Δ = 3249 := by
  have h := freyTwoAdicHalvingModel_discriminant_of_congruences (a := 3) (b := 16) (n := 3)
    (by norm_num)
  rw [h]
  norm_num

theorem freyTwoAdicHalvingModel_three_sixteen_isMinimal :
    WeierstrassCurve.IsMinimal ℤ_[2] (freyTwoAdicHalvingModel 3 16) := by
  letI := freyTwoAdicHalvingModel_three_sixteen_isIntegral
  refine padicWeierstrass_isMinimal_of_discriminant_valuation_one _ ?_
  rw [freyTwoAdicHalvingModel_three_sixteen_discriminant]
  exact freyPadicValuation_eq_one_of_isUnit (z := (3249 : ℤ_[2])) (by
    rw [show (3249 : ℤ_[2]) = ((3249 : ℕ) : ℤ_[2]) by norm_num]
    rw [freyPadic_natCast_isUnit_iff]
    norm_num)

/-- **Good reduction at `2` for the ABC Frey curve with `(a, b) = (3, 16)`**,
witnessed by the explicit halving change: a fully evaluated 2-adic reduction
theorem for an actual ABC triple `(3, 16, 19)`. -/
theorem freyTwoAdicHalvingModel_three_sixteen_hasGoodReduction :
    WeierstrassCurve.HasGoodReduction ℤ_[2] (freyTwoAdicHalvingModel 3 16) := by
  haveI := freyTwoAdicHalvingModel_three_sixteen_isMinimal
  refine WeierstrassCurve.HasGoodReduction.mk ?_
  rw [freyTwoAdicHalvingModel_three_sixteen_discriminant]
  exact freyPadicValuation_eq_one_of_isUnit (z := (3249 : ℤ_[2])) (by
    rw [show (3249 : ℤ_[2]) = ((3249 : ℕ) : ℤ_[2]) by norm_num]
    rw [freyPadic_natCast_isUnit_iff]
    norm_num)

/-! ## Precise cards for the statements not proved in this file

The following `Prop`-valued definitions record the precise remaining
propositions (see `tmp/dsh-2adic-minimal-model-20261016/REPORT.md` §3.2,
§3.3 and §5).  They are *not proved* and must not be used as hypotheses for
further mathematics.

The remaining unobstructed gaps are:

* the full Tate algorithm at `p = 2` (not in Mathlib; needed for the
  additive Kodaira labels; REPORT §3.4, §5.2.1);
* Kodaira label uniqueness is false as a function of the naive invariants —
  Dokchitser–Dokchitser (arXiv:1209.1414, Example 4) exhibit `y² = x³ - 2x`
  over `ℚ₂` with type III and `v₂(Δ) = 9`;
* the conductor exponent of the additive cases needs Ogg–Saito data
  (`m_p`, wild ramification) which is not available (REPORT §5.2.2);
* a general 2-adic minimality criterion for integral models with non-unit
  `c₄` (REPORT §5.2.3), needed for the displayed-model card below. -/

/-- **Card (REPORT §3.2, the `k = 0` rows).**  If neither explicit
first-step change is integral — the halving change `(2, 0, 1, 0)` is not
integral for `(a, b)` (`¬ 4 ∣ b - a - 1` or `¬ 16 ∣ a * b`) and the case C
change does not apply (not `a ≡ 1 (mod 4)` with `16 ∣ a + b`) — then the
*displayed* Frey model itself is minimal at `2`, and by
`freyPadicCurve_two_hasAdditiveReduction_iff_isMinimal` has additive
reduction at `2`.  Computational evidence: exhaustive search over all
coprime `1 ≤ a, b < 130` (`q3_verify_all.py`, 0 mismatches).  Missing: a
general 2-adic minimality criterion for non-unit `c₄` (REPORT §5.2.3). -/
def FreyTwoAdicDisplayedModelMinimalStatement : Prop :=
  ∀ a b : ℕ, IsABCTriple a b (a + b) →
    ¬ ((4 : ℤ) ∣ (b : ℤ) - (a : ℤ) - 1 ∧ (16 : ℤ) ∣ (a : ℤ) * b) →
    ¬ (a % 4 = 1 ∧ 16 ∣ a + b) →
    WeierstrassCurve.IsMinimal ℤ_[2] (freyPadicCurve 2 a b)

/-- **Card (REPORT §3.3).**  In the multiplicative family with `a ≡ 7 (mod 8)`
the halved minimal model has *split* multiplicative reduction at `2`.  Proof
route: evaluate Mathlib's splitting polynomial over the residue field, where
the model `(1, m, 0, -n, 0)` has `a₂ ≡ 0 (mod 2)` and `a₃ = 0`.  Not
formalised in this file. -/
def FreyTwoAdicSplitMultiplicativeStatement : Prop :=
  ∀ a b : ℕ, (∃ m : ℤ, (b : ℤ) = (a : ℤ) + 1 + 4 * m) →
    (∃ n : ℕ, a * b = 16 * n ∧ 2 ∣ n) → a % 8 = 7 →
    WeierstrassCurve.HasSplitMultiplicativeReduction ℤ_[2] (freyTwoAdicHalvingModel a b)

/-- **Card (REPORT §3.3).**  In the multiplicative family with `a ≡ 3 (mod 8)`
the halved minimal model has *non-split* multiplicative reduction at `2`
(the splitting polynomial evaluates to the non-split quadratic `T² + T + 1`
over `𝔽₂`).  Not formalised in this file. -/
def FreyTwoAdicNonSplitMultiplicativeStatement : Prop :=
  ∀ a b : ℕ, (∃ m : ℤ, (b : ℤ) = (a : ℤ) + 1 + 4 * m) →
    (∃ n : ℕ, a * b = 16 * n ∧ 2 ∣ n) → a % 8 = 3 →
    ¬ WeierstrassCurve.HasSplitMultiplicativeReduction ℤ_[2] (freyTwoAdicHalvingModel a b)

end LeanFormal.IUT
