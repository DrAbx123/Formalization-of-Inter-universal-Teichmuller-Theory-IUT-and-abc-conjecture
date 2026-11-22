import LeanFormal.IUT.ABCBridge.Geometry.FreyConductorTwoAdic
import LeanFormal.IUT.ABCBridge.Geometry.FreyTwoAdicMinimalReduction

/-!
# The local `2`-adic exponent on the solvable abc-Frey family

This file evaluates the local exponent function `conductorExponentTwoAdic`
of `FreyConductorTwoAdic` on the minimal halved model of the solvable
family of `FreyTwoAdicMinimalReduction`: for `b = a + 1 + 4 * m` and
`a * b = 16 * n` the model `freyTwoAdicHalvingModel a b` is minimal at `2`,
and the local exponent is

* `0` when `n` is odd (that is `v₂(a * b * c) = 4`; good reduction);
* `1` when `n` is even (that is `v₂(a * b * c) ≥ 5`; multiplicative
  reduction).

These are the first evaluated rows of the `p = 2` case table of
`FreyTwoAdicCaseTableCards`, for the solvable parity shapes A and B
(exactly one of `a`, `b` even).  Only the two branches of
`conductorExponentTwoAdic` carrying mathematical content are used; no
additive-case value, Ogg–Saito datum, or wild-correction constant is
stated, used, or endorsed here.  The additive case C, the placeholder
branch, and the literature freeze of
`logs/coordination/frey-tate-oggsaito-cards-20261016.md` are unchanged.
-/

noncomputable section

namespace LeanFormal.IUT

/-- In the solvable family with `n` odd (good reduction at `2`), the local
exponent on the minimal halved model is `0`. -/
theorem freyTwoAdicHalvingModel_conductorExponentTwoAdic_eq_zero_of_congruences
    {a b : ℕ} {m : ℤ} {n : ℕ} (hb : (b : ℤ) = (a : ℤ) + 1 + 4 * m)
    (hab : a * b = 16 * n) (hn : Odd n) :
    conductorExponentTwoAdic (freyTwoAdicHalvingModel a b) = 0 :=
  conductorExponentTwoAdic_eq_zero_of_hasGoodReduction
    (freyTwoAdicHalvingModel_hasGoodReduction_of_congruences hb hab hn)

/-- In the solvable family with `n` even (multiplicative reduction at `2`),
the local exponent on the minimal halved model is `1`. -/
theorem freyTwoAdicHalvingModel_conductorExponentTwoAdic_eq_one_of_congruences
    {a b : ℕ} {m : ℤ} {n : ℕ} (hb : (b : ℤ) = (a : ℤ) + 1 + 4 * m)
    (hab : a * b = 16 * n) (hn : 2 ∣ n) :
    conductorExponentTwoAdic (freyTwoAdicHalvingModel a b) = 1 :=
  conductorExponentTwoAdic_eq_one_of_hasMultiplicativeReduction
    (freyTwoAdicHalvingModel_hasMultiplicativeReduction_of_congruences hb hab hn)

/-- The two cases combined: on the solvable family the local exponent is
`1` exactly when `n` is even. -/
theorem freyTwoAdicHalvingModel_conductorExponentTwoAdic_eq_ite_of_congruences
    {a b : ℕ} {m : ℤ} {n : ℕ} (hb : (b : ℤ) = (a : ℤ) + 1 + 4 * m)
    (hab : a * b = 16 * n) :
    conductorExponentTwoAdic (freyTwoAdicHalvingModel a b) = if 2 ∣ n then 1 else 0 := by
  by_cases h : 2 ∣ n
  · rw [if_pos h]
    exact freyTwoAdicHalvingModel_conductorExponentTwoAdic_eq_one_of_congruences hb hab h
  · rw [if_neg h]
    refine freyTwoAdicHalvingModel_conductorExponentTwoAdic_eq_zero_of_congruences hb hab ?_
    rw [← Nat.not_even_iff_odd]
    intro he
    exact h (even_iff_two_dvd.mp he)

/-- Evaluated instance `(a, b) = (3, 16)` (`n = 3` odd): local exponent
`0`. -/
theorem freyTwoAdicHalvingModel_three_sixteen_conductorExponentTwoAdic_eq_zero :
    conductorExponentTwoAdic (freyTwoAdicHalvingModel 3 16) = 0 :=
  freyTwoAdicHalvingModel_conductorExponentTwoAdic_eq_zero_of_congruences
    (m := 3) (n := 3) (by norm_num) (by norm_num) ⟨1, by norm_num⟩

/-- Evaluated instance `(a, b) = (7, 32)` (`n = 14` even): local exponent
`1`. -/
theorem freyTwoAdicHalvingModel_seven_thirtytwo_conductorExponentTwoAdic_eq_one :
    conductorExponentTwoAdic (freyTwoAdicHalvingModel 7 32) = 1 :=
  freyTwoAdicHalvingModel_conductorExponentTwoAdic_eq_one_of_congruences
    (m := 6) (n := 14) (by norm_num) (by norm_num) (by norm_num)

end LeanFormal.IUT
