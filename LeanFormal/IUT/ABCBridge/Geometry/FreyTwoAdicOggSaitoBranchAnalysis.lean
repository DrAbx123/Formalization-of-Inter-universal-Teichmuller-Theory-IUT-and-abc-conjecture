/-
# Ogg–Saito branch analysis: the additive rows of the abc-Frey family at `2`

This file continues `FreyTwoAdicOggSaitoConditional`.  There, the
placeholder condition of the additive (`k = 0`) rows of
`conductorExponentTwoAdic` was isolated as

  `(4 + 2β + 1 - m₂) + swan₂ = 2`,  `β = v₂(a b (a + b))`

in natural-number arithmetic (with truncation at zero).  Here that condition
is resolved symbolically.  No numerical value of `m₂` or `swan₂` is
asserted, computed, or endorsed anywhere in this file.

* case lemmas: for `swan₂ = 0`, `1`, `2` the condition is equivalent to
  `m₂ = 3 + 2β`, `m₂ = 4 + 2β`, `5 + 2β ≤ m₂` respectively; the last regime
  lives on the truncation of `(v₂Δmin + 1) - m₂` at zero;
* regime trichotomy: the condition holds exactly in those three regimes
  (the two-branch form of `freyTwoAdicSaitoSlotArithmetic_eq_two_iff` split
  by the value of `swan₂`);
* wild refutation: `swan₂ ≥ 3` makes the condition fail, so the placeholder
  must be replaced in that regime;
* necessary conditions: agreement forces `3 + 2β ≤ m₂` and `swan₂ ≤ 2`;
* no-truncation collapse: under the structural component bound
  `m₂ ≤ v₂Δmin + 1` the three regimes collapse to the single branch-one
  equation `m₂ = 3 + 2β + swan₂`;
* multiplicative rows: for a slot record satisfying the Ogg–Saito relation
  with the no-truncation bound, `f₂ = 1` is equivalent to
  `m₂ = v₂Δmin + swan₂` — Ogg's formula in the multiplicative form
  `c = 1 ⟺ m = ord(q) = ord(Δmin) + swan`;
* PARK card: `FreyTwoAdicAdditiveOggSaitoSlotRegimeCard` isolates the exact
  arithmetic input still missing, with a consumer that closes the additive
  placeholder once the card and the Ogg–Saito relation are supplied.

Literature freeze (statement level only, as in `TateOggSaitoTwoAdicCards`):

* Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, IV.9
  (Tate's algorithm; type table with classical component counts
  `II: 1`, `III: 2`, `IV: 3`, `I₀*: 5`, `I_n*: n + 5`, `IV*: 7`,
  `III*: 8`, `II*: 9`), IV.10 (the conductor: exponent `1` exactly for
  multiplicative reduction, `≥ 2` for additive), IV.11 (Ogg's formula
  `c = ord(Δmin) + 1 - m`).
* Saito, Duke Math. J. 57(1) (1988) 151-173: the wild correction term;
  cited only, full text remains inaccessible — no exponent table from it is
  transcribed anywhere in this file.
* Dokchitser–Dokchitser, arXiv:1209.1414: in residue characteristic `2` the
  Kodaira label is not determined by `(vΔ, v c₄, v c₆)`; the frozen case
  analysis (`tmp/dsh-2adic-minimal-model-20261016/REPORT.md`, sections
  3.2-3.4) leaves candidate labels in the `III`, `IV`, `I₀*`, `I_n*`, `IV*`,
  `III*` families for the additive rows, so the slot pair `(m₂, swan₂)` is
  not identifiable from the proved invariants `v₂Δmin = 4 + 2β`,
  `v₂c₄ = 4`, `v₂c₆ = 6` of the `k = 0` value card.  A full 2-adic Tate
  algorithm and the wild tables behind `swan₂` are exactly the missing
  arithmetic inputs; no row and no label is claimed here.

Object / quantifiers / assumptions / consumer: the object is the displayed
abc-Frey curve `freyPadicCurve 2 a b` over `ℚ_[2]` with free slot values (or
free slot functions); the quantifiers are `∀ a b : ℕ` (ABC triples) and
`∀ m₂ swan₂ : ℕ`; the assumptions are the Ogg–Saito relation
`conductorExponentTwoAdicFormula`, the `k = 0` minimality conditions
(`FreyTwoAdicNoUniformizerChange`) where the domain is the additive rows,
and the no-truncation bound `m₂ ≤ v₂Δmin + 1` where branch collapse is
claimed; the consumer is the additive branch of `conductorExponentTwoAdic`
(`FreyConductorTwoAdic`), whose value `2` is a placeholder.  Nothing here
decides the placeholder: the analysis turns that decision into the exact
regime membership of `(m₂, swan₂)`.
-/

import LeanFormal.IUT.ABCBridge.Geometry.FreyTwoAdicOggSaitoConditional

noncomputable section

namespace LeanFormal.IUT

open LeanFormal.IUT.ABCBridge.Geometry.TateOggSaitoTwoAdicCards

/-! ## Slot arithmetic: case lemmas and the regime trichotomy -/

/-- **Tame case** (`swan₂ = 0`): the placeholder condition forces the
component count `m₂ = 3 + 2β`. -/
theorem freyTwoAdicSaitoSlotArithmetic_eq_two_iff_swanZero (m₂ β : ℕ) :
    ((4 + 2 * β + 1 - m₂) + 0 = 2) ↔ m₂ = 3 + 2 * β := by
  omega

/-- **One wild unit** (`swan₂ = 1`): the still-holding regime forces
`m₂ = 4 + 2β`. -/
theorem freyTwoAdicSaitoSlotArithmetic_eq_two_iff_swanOne (m₂ β : ℕ) :
    ((4 + 2 * β + 1 - m₂) + 1 = 2) ↔ m₂ = 4 + 2 * β := by
  omega

/-- **Two wild units** (`swan₂ = 2`): the truncation of
`(v₂Δmin + 1) - m₂` at zero lets the value `2` survive for every
`m₂ ≥ 5 + 2β`. -/
theorem freyTwoAdicSaitoSlotArithmetic_eq_two_iff_swanTwo (m₂ β : ℕ) :
    ((4 + 2 * β + 1 - m₂) + 2 = 2) ↔ 5 + 2 * β ≤ m₂ := by
  omega

/-- **Wild refutation**: if the Swan term is at least `3`, the slot
arithmetic can never return `2`. -/
theorem freyTwoAdicSaitoSlotArithmetic_ne_two_of_swan_ge_three (m₂ swan₂ β : ℕ)
    (hswan : 3 ≤ swan₂) :
    (4 + 2 * β + 1 - m₂) + swan₂ ≠ 2 := by
  omega

/-- **Regime trichotomy**: the placeholder condition holds exactly in the
three displayed regimes; every other slot pair (in particular `swan₂ ≥ 3`)
refutes the placeholder. -/
theorem freyTwoAdicSaitoSlotArithmetic_eq_two_iff_regimes (m₂ swan₂ β : ℕ) :
    ((4 + 2 * β + 1 - m₂) + swan₂ = 2) ↔
      (swan₂ = 0 ∧ m₂ = 3 + 2 * β) ∨
        (swan₂ = 1 ∧ m₂ = 4 + 2 * β) ∨
          (swan₂ = 2 ∧ 5 + 2 * β ≤ m₂) := by
  rw [freyTwoAdicSaitoSlotArithmetic_eq_two_iff]
  omega

/-- **Necessary conditions**: whenever the slot arithmetic returns `2`, the
component count is at least `3 + 2β` and the Swan term is at most `2`; a
failure of either bound refutes the placeholder. -/
theorem freyTwoAdicSaitoSlotArithmetic_eq_two_necessary (m₂ swan₂ β : ℕ)
    (h : (4 + 2 * β + 1 - m₂) + swan₂ = 2) :
    3 + 2 * β ≤ m₂ ∧ swan₂ ≤ 2 := by
  omega

/-- **No-truncation collapse**: under the structural bound
`m₂ ≤ v₂Δmin + 1` (component counts of the special fibre never exceed
`vΔ + 1`; input from the missing Néron-component theory), the three regimes
collapse to branch one, i.e. to the single equation `m₂ = 3 + 2β + swan₂`. -/
theorem freyTwoAdicSaitoSlotArithmetic_eq_two_iff_of_noTruncation (m₂ swan₂ β : ℕ)
    (hm : m₂ ≤ 4 + 2 * β + 1) :
    ((4 + 2 * β + 1 - m₂) + swan₂ = 2) ↔ m₂ = 3 + 2 * β + swan₂ := by
  rw [freyTwoAdicSaitoSlotArithmetic_eq_two_iff]
  omega

/-! ## Transport to the displayed abc-Frey additive rows -/

/-- **Regime trichotomy for the Frey placeholder**: on an ABC triple and
under the Ogg–Saito relation, the placeholder `conductorExponentTwoAdic = 2`
agrees with the conditional value exactly in the three slot regimes. -/
theorem freyTwoAdicAdditivePlaceholder_agreement_regimes {a b : ℕ}
    (htri : IsABCTriple a b (a + b)) (m₂ swan₂ : ℕ) {f₂ : ℕ}
    (hrel : conductorExponentTwoAdicFormula (freyPadicCurve 2 a b)
      (freyTwoAdicAdditiveSaitoSlots a b m₂ swan₂) f₂) :
    (conductorExponentTwoAdic (freyPadicCurve 2 a b) = f₂) ↔
      (swan₂ = 0 ∧ m₂ = 3 + 2 * padicValNat 2 (a * b * (a + b))) ∨
        (swan₂ = 1 ∧ m₂ = 4 + 2 * padicValNat 2 (a * b * (a + b))) ∨
          (swan₂ = 2 ∧ 5 + 2 * padicValNat 2 (a * b * (a + b)) ≤ m₂) := by
  rw [freyTwoAdicAdditivePlaceholder_eq_iff htri m₂ swan₂ hrel]
  exact freyTwoAdicSaitoSlotArithmetic_eq_two_iff_regimes m₂ swan₂
    (padicValNat 2 (a * b * (a + b)))

/-- **Branch-one agreement**: if the slots satisfy `m₂ = 3 + 2β + swan₂` with
`swan₂ ≤ 2` (branch one of the earlier two-branch form), the placeholder is
consistent with the Ogg–Saito value. -/
theorem freyTwoAdicAdditivePlaceholder_eq_of_componentCountEq {a b : ℕ}
    (htri : IsABCTriple a b (a + b)) (m₂ swan₂ : ℕ) {f₂ : ℕ}
    (hrel : conductorExponentTwoAdicFormula (freyPadicCurve 2 a b)
      (freyTwoAdicAdditiveSaitoSlots a b m₂ swan₂) f₂)
    (hswan : swan₂ ≤ 2)
    (hm : m₂ = 3 + 2 * padicValNat 2 (a * b * (a + b)) + swan₂) :
    conductorExponentTwoAdic (freyPadicCurve 2 a b) = f₂ := by
  rw [freyTwoAdicAdditivePlaceholder_eq_iff htri m₂ swan₂ hrel]
  omega

/-- **Wild refutation, transported**: `swan₂ ≥ 3` on the additive rows makes
the placeholder disagree with the Ogg–Saito value; the displayed placeholder
must then be replaced. -/
theorem freyTwoAdicAdditivePlaceholder_ne_of_swan_ge_three {a b : ℕ}
    (htri : IsABCTriple a b (a + b)) (m₂ swan₂ : ℕ) {f₂ : ℕ}
    (hrel : conductorExponentTwoAdicFormula (freyPadicCurve 2 a b)
      (freyTwoAdicAdditiveSaitoSlots a b m₂ swan₂) f₂)
    (hswan : 3 ≤ swan₂) :
    conductorExponentTwoAdic (freyPadicCurve 2 a b) ≠ f₂ := by
  intro hph
  exact freyTwoAdicSaitoSlotArithmetic_ne_two_of_swan_ge_three m₂ swan₂
    (padicValNat 2 (a * b * (a + b))) hswan
    ((freyTwoAdicAdditivePlaceholder_eq_iff htri m₂ swan₂ hrel).mp hph)

/-- **No-truncation decision**: under the component bound
`m₂ ≤ 4 + 2β + 1`, placeholder agreement is equivalent to the single
equation `m₂ = 3 + 2β + swan₂`; the truncation regime disappears. -/
theorem freyTwoAdicAdditivePlaceholder_eq_iff_of_componentCountBound {a b : ℕ}
    (htri : IsABCTriple a b (a + b)) (m₂ swan₂ : ℕ) {f₂ : ℕ}
    (hrel : conductorExponentTwoAdicFormula (freyPadicCurve 2 a b)
      (freyTwoAdicAdditiveSaitoSlots a b m₂ swan₂) f₂)
    (hm : m₂ ≤ 4 + 2 * padicValNat 2 (a * b * (a + b)) + 1) :
    (conductorExponentTwoAdic (freyPadicCurve 2 a b) = f₂) ↔
      m₂ = 3 + 2 * padicValNat 2 (a * b * (a + b)) + swan₂ := by
  rw [freyTwoAdicAdditivePlaceholder_eq_iff htri m₂ swan₂ hrel]
  exact freyTwoAdicSaitoSlotArithmetic_eq_two_iff_of_noTruncation m₂ swan₂
    (padicValNat 2 (a * b * (a + b))) hm

/-- **Necessary conditions, transported**: placeholder agreement forces
`3 + 2β ≤ m₂` and `swan₂ ≤ 2`. -/
theorem freyTwoAdicAdditivePlaceholder_necessary_of_agreement {a b : ℕ}
    (htri : IsABCTriple a b (a + b)) (m₂ swan₂ : ℕ) {f₂ : ℕ}
    (hrel : conductorExponentTwoAdicFormula (freyPadicCurve 2 a b)
      (freyTwoAdicAdditiveSaitoSlots a b m₂ swan₂) f₂)
    (hph : conductorExponentTwoAdic (freyPadicCurve 2 a b) = f₂) :
    3 + 2 * padicValNat 2 (a * b * (a + b)) ≤ m₂ ∧ swan₂ ≤ 2 := by
  have h2 : (4 + 2 * padicValNat 2 (a * b * (a + b)) + 1 - m₂) + swan₂ = 2 :=
    (freyTwoAdicAdditivePlaceholder_eq_iff htri m₂ swan₂ hrel).mp hph
  exact freyTwoAdicSaitoSlotArithmetic_eq_two_necessary m₂ swan₂
    (padicValNat 2 (a * b * (a + b))) h2

/-! ## The multiplicative rows: Ogg's formula in slot form -/

/-- **Multiplicative rows, Ogg reading**: for any slot record satisfying the
Ogg–Saito relation and the no-truncation bound, `f₂ = 1` (Silverman IV.10:
conductor exponent `1` exactly for multiplicative reduction) is equivalent
to `m₂ = v₂Δmin + swan₂`; for a tame record (`swan₂ = 0`) this is the
classical `m = ord(q) = ord(Δmin)`. -/
theorem freyTwoAdicOggSaitoMultiplicativeRow_iff {a b : ℕ}
    (d : TateOggSaitoTwoAdicData (freyPadicCurve 2 a b)) {f₂ : ℕ}
    (hrel : conductorExponentTwoAdicFormula (freyPadicCurve 2 a b) d f₂)
    (hm : d.m₂ ≤ d.v₂Δmin + 1) :
    (f₂ = 1) ↔ d.m₂ = d.v₂Δmin + d.swan₂ := by
  rw [conductorExponentTwoAdicFormula] at hrel
  omega

/-- **Multiplicative rows, component count**: `f₂ = 1` under the
no-truncation bound yields the component count `m₂ = v₂Δmin + swan₂` and the
Swan bound `swan₂ ≤ 1`. -/
theorem freyTwoAdicOggSaitoMultiplicativeRow_componentCount {a b : ℕ}
    (d : TateOggSaitoTwoAdicData (freyPadicCurve 2 a b)) {f₂ : ℕ}
    (hrel : conductorExponentTwoAdicFormula (freyPadicCurve 2 a b) d f₂)
    (hm : d.m₂ ≤ d.v₂Δmin + 1) (hf : f₂ = 1) :
    d.m₂ = d.v₂Δmin + d.swan₂ ∧ d.swan₂ ≤ 1 := by
  have h := (freyTwoAdicOggSaitoMultiplicativeRow_iff d hrel hm).mp hf
  exact ⟨h, by omega⟩

/-! ## The PARK card: the exact remaining input of the additive branch -/

/-- **PARK — additive-row slot-regime card**: the arithmetic input still
missing for the additive (`k = 0`) rows, parameterized by the slot functions
`m₂`, `swan₂` of the 2-adic minimal model.  Supplying those functions (full
2-adic Tate algorithm; labels are not determined by `(vΔ, v c₄, v c₆)` in
residue characteristic 2, Dokchitser–Dokchitser arXiv:1209.1414) together
with a proof of this `Prop` (Saito 1988's wild tables enter through `swan₂`)
is exactly what is still open; neither the functions nor this regime
membership are constructed or proved here, and no value is endorsed. -/
def FreyTwoAdicAdditiveOggSaitoSlotRegimeCard (m₂ swan₂ : ℕ → ℕ → ℕ) : Prop :=
  ∀ a b : ℕ, IsABCTriple a b (a + b) →
    ¬ ((4 : ℤ) ∣ (b : ℤ) - (a : ℤ) - 1 ∧ (16 : ℤ) ∣ (a : ℤ) * b) →
      ¬ (a % 4 = 1 ∧ 16 ∣ a + b) →
        swan₂ a b ≤ 2 ∧
          m₂ a b = 3 + 2 * padicValNat 2 (a * b * (a + b)) + swan₂ a b

/-- **Consumer of the slot-regime card**: given a slot family satisfying the
Ogg–Saito relation on the additive (`k = 0`) ABC triples and the regime card,
the placeholder `conductorExponentTwoAdic = 2` agrees with the Ogg–Saito
value `f₂` on every such triple — conditional on exactly the missing input. -/
theorem freyTwoAdicAdditivePlaceholder_eq_of_slotRegimeCard {m₂ swan₂ f₂ : ℕ → ℕ → ℕ}
    (hcard : FreyTwoAdicAdditiveOggSaitoSlotRegimeCard m₂ swan₂)
    (hrel : ∀ (a b : ℕ) (_ : IsABCTriple a b (a + b)),
      conductorExponentTwoAdicFormula (freyPadicCurve 2 a b)
        (freyTwoAdicAdditiveSaitoSlots a b (m₂ a b) (swan₂ a b)) (f₂ a b))
    {a b : ℕ} (htri : IsABCTriple a b (a + b))
    (hhalving : ¬ ((4 : ℤ) ∣ (b : ℤ) - (a : ℤ) - 1 ∧ (16 : ℤ) ∣ (a : ℤ) * b))
    (hcaseC : ¬ (a % 4 = 1 ∧ 16 ∣ a + b)) :
    conductorExponentTwoAdic (freyPadicCurve 2 a b) = f₂ a b := by
  obtain ⟨hswan, hm⟩ := hcard a b htri hhalving hcaseC
  exact freyTwoAdicAdditivePlaceholder_eq_of_componentCountEq htri (m₂ a b)
    (swan₂ a b) (hrel a b htri) hswan hm

end LeanFormal.IUT
