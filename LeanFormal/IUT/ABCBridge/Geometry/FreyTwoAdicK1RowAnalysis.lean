/-
# The `k = 1` rows of the 2-adic ABC Frey table: no additive case

Frozen semantics of the row parameter `k`
(`tmp/dsh-2adic-minimal-model-20261016/REPORT.md` §3.2, line 79: "`k = 1`
means the half-model is minimal, `k = 0` the displayed model"):

* `k = 0` rows: the displayed model `freyPadicCurve 2 a b` itself is minimal;
  in Lean its hypotheses are `¬ (4 ∣ b - a - 1 ∧ 16 ∣ a * b)` and
  `¬ (a % 4 = 1 ∧ 16 ∣ a + b)` (the two `k = 0` negations of
  `FreyTwoAdicDisplayedModelNoUniformizerChangeStatement`).
* `k = 1` rows: the displayed model is not minimal; a first Tate step
  reaches the minimal model.  For the halving change `(u, r, s, t) =
  (2, 0, 1, 0)` the integrality congruences are `b = a + 1 + 4 m` and
  `a * b = 16 n`; for ABC triples with `a * b` even these are exactly the
  case A / case B `k = 1` conditions `a ≡ 3 (4) ∧ β ≥ 4` resp.
  `b ≡ 1 (4) ∧ α ≥ 4` of REPORT §3.2.  The case C `k = 1` rows
  (`a ≡ 1 (4)`, `16 ∣ a + b`, both `a`, `b` odd) use the different witness
  change `(2, 1, 1, 0)` / `(2, 1, 1, 4)` and are carded below.

Additive reduction occurs exactly on the `k = 0` rows (every additive row of
REPORT §3.2 carries `k = 0`; the `k = 1` rows carry good or multiplicative
reduction).  Hence:

* the conditional card `freyTwoAdicAdditiveCaseValueCard` cannot be "pushed
  to `k = 1`" as an additive statement — there are no `k ≥ 1` additive rows;
  the correct extension is the non-minimality / non-additivity proved here;
  the `k = 0` closure of `FreyTwoAdicNoUniformizerChange` already
  de-conditioned the card on all `k = 0` (hence all additive) rows;
* the `k = 1` halving rows need no residue kernel: the half-model's
  minimality is already proved directly by the unit-`c₄` criterion
  (`abcInvariantPolynomial a b` is odd), and minimality is definitional
  maximality, so no "no second descent" enumeration arises.  A "no change of
  the half-model with `u` of valuation `exp (-1)`" kernel would, if written
  in the `mod 32` style of the `k = 0` file, be *larger*: the half-model
  coefficients `(1, m, 0, -n, 0)`, `m = (b - a - 1) / 4`, `n = a * b / 16`,
  make the congruences see `(m mod 16, n mod 16, r mod 32, s mod 2,
  t mod 32)` (≈ `2¹⁹` cases) up to `(a mod 256, b mod 256, r mod 32,
  s mod 2, t mod 32)` (≈ `2²⁷` cases), against the `k = 0` core of
  `2¹⁷ = 131072` cases whose single-`decide` form already exceeded memory
  (timing2 evidence; the four-way split into `2¹⁵`-case kernels succeeded).
  This file therefore introduces no new `decide` enumeration.
* the case C `k = 1` rows are not a kernel-size question: the witness change
  and its integrality congruences (including solubility of
  `t² ≡ (1 - a) (1 + b) (mod 64)`) are a new object, carded as
  `FreyTwoAdicCaseCK1MinimalModelStatement`.

Proved in this file (halving rows, i.e. cases A and B):

* `freyTwoAdicDisplayedModel_not_isMinimal_of_halving_congruences`: the
  displayed model is not minimal — the half-model is integral with
  `Δ`-valuation `exp (-(2 v₂(n (a + b))))` strictly larger than the
  displayed `exp (-(4 + 2 v₂(a b (a + b))))` (the two exponents differ by
  the constant `12`), contradicting the maximality clause of `IsMinimal`.
* `freyTwoAdicDisplayedModel_not_hasAdditiveReduction_of_halving_congruences`:
  hence the displayed model has no additive reduction there (its
  `HasAdditiveReduction` requires minimality).
* `freyTwoAdicHalvingModel_not_hasAdditiveReduction_of_congruences`: the
  `k = 1` minimal model (the half-model) has no additive reduction either:
  it is good or multiplicative according to the parity of `n`.

Literature freeze (statement-level): Silverman, *Advanced Topics in the
Arithmetic of Elliptic Curves*, IV.9 and IV.10; Saito 1988 (cited only).
The `m₂` and `swan₂` exponents are not treated in this file.
-/

import LeanFormal.IUT.ABCBridge.Geometry.FreyTwoAdicMinimalDiscriminantValuation
import LeanFormal.IUT.ABCBridge.Geometry.FreyTwoAdicAdditiveCaseValueCard

noncomputable section

open scoped WeierstrassCurve WithZero

namespace LeanFormal.IUT

/-! ## The `k = 1` halving rows: the displayed model is not minimal -/

/-- **The displayed model is not minimal on the halving rows.**  For an ABC
triple with `b = a + 1 + 4 m` and `a * b = 16 n`, the integral half-model has
strictly larger `Δ`-valuation than the displayed model, contradicting
maximality if the displayed model were minimal. -/
theorem freyTwoAdicDisplayedModel_not_isMinimal_of_halving_congruences
    {a b : ℕ} (htri : IsABCTriple a b (a + b)) {m : ℤ} {n : ℕ}
    (hb : (b : ℤ) = (a : ℤ) + 1 + 4 * m) (hab : a * b = 16 * n) :
    ¬ WeierstrassCurve.IsMinimal ℤ_[2] (freyPadicCurve 2 a b) := by
  intro hmin
  have ha0 : a ≠ 0 := Nat.ne_of_gt htri.1
  have hb0 : b ≠ 0 := Nat.ne_of_gt htri.2.1
  have hc0 : a + b ≠ 0 := by
    have ha := htri.1
    omega
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact (mul_ne_zero ha0 hb0) (by simpa using hab)
  have hV0 : n * (a + b) ≠ 0 := mul_ne_zero hn0 hc0
  haveI hint : WeierstrassCurve.IsIntegral ℤ_[2] (freyTwoAdicHalvingModel a b) :=
    freyTwoAdicHalvingModel_isIntegral_of_congruences hb hab
  haveI hintC : WeierstrassCurve.IsIntegral ℤ_[2]
      (freyTwoAdicHalvingChange • freyPadicCurve 2 a b) := by
    simpa only [freyTwoAdicHalvingModel] using hint
  haveI hintD : WeierstrassCurve.IsIntegral ℤ_[2] (freyPadicCurve 2 a b) :=
    freyPadicCurve_isIntegral 2 a b
  haveI hminI : WeierstrassCurve.IsMinimal ℤ_[2] (freyPadicCurve 2 a b) := hmin
  have hle := valuation_Δ_aux_le_of_isMinimal (R := ℤ_[2]) (K := ℚ_[2])
    (W := freyPadicCurve 2 a b) freyTwoAdicHalvingChange
  have hle' : (WeierstrassCurve.valuation_Δ_aux ℤ_[2]
        (freyTwoAdicHalvingChange • freyPadicCurve 2 a b)).val ≤
      (WeierstrassCurve.valuation_Δ_aux ℤ_[2] (freyPadicCurve 2 a b)).val :=
    hle
  rw [freyPadicValuation_eq_valuation_Δ_aux_val
        (W := freyTwoAdicHalvingChange • freyPadicCurve 2 a b),
      freyPadicValuation_eq_valuation_Δ_aux_val
        (W := freyPadicCurve 2 a b)] at hle'
  rw [show freyTwoAdicHalvingChange • freyPadicCurve 2 a b =
      freyTwoAdicHalvingModel a b from rfl,
    freyTwoAdicHalvingModel_discriminant_of_congruences hab,
    freyPadicValuation_two_natCast_eq_exp_neg_padicValNat (pow_ne_zero 2 hV0),
    padicValNat.pow,
    freyPadicCurve_two_discriminant_valuation_eq_exp_neg htri] at hle'
  have hβV : padicValNat 2 (a * b * (a + b)) =
      4 + padicValNat 2 (n * (a + b)) := by
    rw [padicValNat.mul (mul_ne_zero ha0 hb0) hc0,
      padicValNat.mul hn0 hc0,
      show a * b = 16 * n from hab,
      padicValNat.mul (by norm_num : (16 : ℕ) ≠ 0) hn0]
    have h16 : padicValNat 2 16 = 4 := by
      rw [show (16 : ℕ) = 2 ^ 4 by norm_num, padicValNat.pow, padicValNat_self]
    rw [h16]
    omega
  have hmono := WithZero.exp_le_exp.mp hle'
  omega

/-- **The additive value card does not extend to the halving rows.**  On the
halving rows the displayed model has no additive reduction at `2`: the
model-level `HasAdditiveReduction` would require minimality of the displayed
model, which the previous theorem refutes. -/
theorem freyTwoAdicDisplayedModel_not_hasAdditiveReduction_of_halving_congruences
    {a b : ℕ} (htri : IsABCTriple a b (a + b)) {m : ℤ} {n : ℕ}
    (hb : (b : ℤ) = (a : ℤ) + 1 + 4 * m) (hab : a * b = 16 * n) :
    ¬ WeierstrassCurve.HasAdditiveReduction ℤ_[2] (freyPadicCurve 2 a b) :=
  fun hred =>
    freyTwoAdicDisplayedModel_not_isMinimal_of_halving_congruences htri hb hab
      hred.toIsMinimal

/-- **The `k = 1` minimal model is never additive.**  In the halving family
the half-model is minimal with unit `c₄ = abcInvariantPolynomial a b`; its
reduction is good (`n` odd) or multiplicative (`n` even), never additive. -/
theorem freyTwoAdicHalvingModel_not_hasAdditiveReduction_of_congruences
    {a b : ℕ} {m : ℤ} {n : ℕ}
    (hb : (b : ℤ) = (a : ℤ) + 1 + 4 * m) (hab : a * b = 16 * n) :
    ¬ WeierstrassCurve.HasAdditiveReduction ℤ_[2] (freyTwoAdicHalvingModel a b) := by
  rcases Nat.even_or_odd n with he | ho
  · exact (freyTwoAdicHalvingModel_hasMultiplicativeReduction_of_congruences
      hb hab he.two_dvd).not_hasAdditiveReduction
  · exact (freyTwoAdicHalvingModel_hasGoodReduction_of_congruences
      hb hab ho).not_hasAdditiveReduction

/-! ## The case A / case B `k = 1` parity data imply the halving congruences -/

/-- Case A `k = 1` parity data (`a ≡ 3 (4)`, `16 ∣ b`) supplies the halving
congruence `b = a + 1 + 4 m`. -/
theorem freyTwoAdicCaseAHalvingCongruence {a b : ℕ}
    (ha : a % 4 = 3) (hb : 16 ∣ b) :
    ∃ m : ℤ, (b : ℤ) = (a : ℤ) + 1 + 4 * m := by
  obtain ⟨k, rfl⟩ := hb
  have hnat : a + 1 = 4 * (a / 4 + 1) := by
    have h := Nat.div_add_mod a 4
    omega
  have hcast : (a : ℤ) + 1 = 4 * ((a / 4 + 1 : ℕ) : ℤ) := by
    exact_mod_cast hnat
  exact ⟨4 * (k : ℤ) - ((a / 4 + 1 : ℕ) : ℤ), by omega⟩

/-- Case B `k = 1` parity data (`b ≡ 1 (4)`, `16 ∣ a`) supplies the halving
congruence `b = a + 1 + 4 m`. -/
theorem freyTwoAdicCaseBHalvingCongruence {a b : ℕ}
    (ha : 16 ∣ a) (hb : b % 4 = 1) :
    ∃ m : ℤ, (b : ℤ) = (a : ℤ) + 1 + 4 * m := by
  obtain ⟨k, rfl⟩ := ha
  have hnat : b = 4 * (b / 4) + 1 := by
    have h := Nat.div_add_mod b 4
    omega
  have hcast : (b : ℤ) = 4 * ((b / 4 : ℕ) : ℤ) + 1 := by
    exact_mod_cast hnat
  exact ⟨((b / 4 : ℕ) : ℤ) - 4 * (k : ℤ), by omega⟩

/-- **The case A `k = 1` row: displayed model not minimal.** -/
theorem freyTwoAdicDisplayedModel_not_isMinimal_of_caseAHalvingData {a b : ℕ}
    (htri : IsABCTriple a b (a + b)) (ha : a % 4 = 3) (hb : 16 ∣ b) :
    ¬ WeierstrassCurve.IsMinimal ℤ_[2] (freyPadicCurve 2 a b) := by
  obtain ⟨m, hm⟩ := freyTwoAdicCaseAHalvingCongruence ha hb
  obtain ⟨k, rfl⟩ := hb
  exact freyTwoAdicDisplayedModel_not_isMinimal_of_halving_congruences htri hm
    (n := a * k) (by ring)

/-- **The case B `k = 1` row: displayed model not minimal.** -/
theorem freyTwoAdicDisplayedModel_not_isMinimal_of_caseBHalvingData {a b : ℕ}
    (htri : IsABCTriple a b (a + b)) (ha : 16 ∣ a) (hb : b % 4 = 1) :
    ¬ WeierstrassCurve.IsMinimal ℤ_[2] (freyPadicCurve 2 a b) := by
  obtain ⟨m, hm⟩ := freyTwoAdicCaseBHalvingCongruence ha hb
  obtain ⟨k, rfl⟩ := ha
  exact freyTwoAdicDisplayedModel_not_isMinimal_of_halving_congruences htri hm
    (n := b * k) (by ring)

/-! ## The case C `k = 1` row: precise card -/

/-- **Precise card (case C `k = 1`, not proved).**  On the case C rows
`a ≡ 1 (4)`, `16 ∣ a + b` (both `a`, `b` odd) the minimal model at `2` is
reached by the witness change `(u, r, s, t) = (2, 1, 1, 0)` if `a ≡ 1 (8)`
and `(2, 1, 1, 4)` if `a ≡ 5 (8)` (REPORT §3.2), and the minimal
discriminant has `v₂ = 2 v₂(a + b) - 8`.  This is **not proved** here: the
integrality of that change is a new arithmetic condition on `t` (including
solubility of `t² ≡ (1 - a) (1 + b) (mod 64)`), not a finite residue
enumeration, and the change is not constructed anywhere in the repository.
The statement is frozen for the record and must not be used as a hypothesis
of further mathematics.  Missing inputs: the five coefficient formulas of
the change `(2, 1, 1, t)` (as `FreyTwoAdicMinimalReduction` does for
`(2, 0, 1, 0)`), the congruence selection for `t`, unit `c₄`, and the
good/multiplicative refinement of the rows `γ = 4` resp. `γ ≥ 5`. -/
def FreyTwoAdicCaseCK1MinimalModelStatement : Prop :=
  ∀ a b : ℕ, IsABCTriple a b (a + b) → a % 4 = 1 → 16 ∣ a + b →
    ∃ C : WeierstrassCurve.VariableChange ℚ_[2],
      WeierstrassCurve.IsIntegral ℤ_[2] (C • freyPadicCurve 2 a b) ∧
        WeierstrassCurve.IsMinimal ℤ_[2] (C • freyPadicCurve 2 a b) ∧
        freyPadicValuation 2 (C • freyPadicCurve 2 a b).Δ =
          WithZero.exp (-((2 * padicValNat 2 (a + b) - 8 : ℕ) : ℤ))

end LeanFormal.IUT
