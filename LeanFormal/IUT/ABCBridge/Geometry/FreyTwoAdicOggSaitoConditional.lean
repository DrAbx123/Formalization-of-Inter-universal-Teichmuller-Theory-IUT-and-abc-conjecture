/-
# The `m₂` / `swan₂` slots of the Ogg–Saito formula at `2`: conditional landing

The two missing entries of the 2-adic conductor computation of the abc-Frey
family are the Ogg–Saito component count `m₂` and the wild (Swan) correction
`swan₂`.  This file lands the **conditional form** of the missing item and
freezes what remains open.  No numerical value of `m₂` or `swan₂` is
asserted or endorsed anywhere in this file.

Literature freeze (statement-level, as in `TateOggSaitoTwoAdicCards` and the
`k = 0` files):

* Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, IV.9
  (Tate's algorithm), IV.10 (the conductor; Theorem 10.2 (a) and Example
  10.5 as cited in `papers/motizuki_corpus/text/Explicit estimates in
  IUTeich.txt`), IV.11 (Ogg's formula 11.1);
* Saito, "Conductor, discriminant, and the Noether formula of arithmetic
  surfaces", Duke Math. J. 57(1) (1988) 151–173 — cited only; the full text
  remains inaccessible (publisher blocked), so no local exponent table is
  transcribed here.

Conditional landing (object / quantifiers / assumptions / consumer):

* object: the displayed abc-Frey curve `freyPadicCurve 2 a b` over `ℚ_[2]`
  together with a `TateOggSaitoTwoAdicData` slot record `d`;
* quantifiers: `∀ a b : ℕ`, `∀ d`, `∀ f₂ : ℕ`;
* assumptions: (i) `IsABCTriple a b (a + b)`; (ii) the `v₂Δmin` slot is
  instantiated to the proved `k = 0` exponent `4 + 2 v₂(a b (a + b))`
  (`freyTwoAdicAdditiveSaitoSlots`; the exponent is exactly the one proved
  by `freyTwoAdicAdditiveCaseValueCard_k0` of
  `FreyTwoAdicNoUniformizerChange`); (iii) the Ogg–Saito relation
  `conductorExponentTwoAdicFormula` holds for `d` and `f₂` (Saito 1988;
  hypothesis only);
* conclusion: `f₂ = 4 + 2 v₂(a b (a + b)) + 1 - m₂ + swan₂`, together with
  the placeholder comparison `conductorExponentTwoAdic = f₂ ↔
  ((4 + 2 v₂(a b (a + b)) + 1 - m₂) + swan₂ = 2)`;
* consumer: the additive branch of `conductorExponentTwoAdic`
  (`FreyConductorTwoAdic`), whose current value `2` is a placeholder.

Exact open condition isolated: the placeholder agrees with the conditional
Ogg–Saito value precisely when `(4 + 2 β + 1 - m₂) + swan₂ = 2` in natural
arithmetic (`β = v₂(a b (a + b))`); arithmetically this is
`(swan₂ ≤ 2 ∧ m₂ = 3 + 2 β + swan₂) ∨ (swan₂ = 2 ∧ 5 + 2 β < m₂)`.  The
identification of the two slots for the additive rows (Saito 1988's local
tables, or a formalized component count and wild-ramification theory) is the
precise missing input; nothing here claims the placeholder is correct.
-/

import LeanFormal.IUT.ABCBridge.Geometry.TateOggSaitoTwoAdicCards
import LeanFormal.IUT.ABCBridge.Geometry.FreyConductorTwoAdic

noncomputable section

namespace LeanFormal.IUT

open LeanFormal.IUT.ABCBridge.Geometry.TateOggSaitoTwoAdicCards

/-- Canonical Ogg–Saito slot record of the `k = 0` (additive) rows: the
`v₂Δmin` slot carries the proved exponent `4 + 2 v₂(a b (a + b))`, while
`m₂` and `swan₂` remain free (open) slots; no value of these two is
endorsed. -/
def freyTwoAdicAdditiveSaitoSlots (a b : ℕ) (m₂ swan₂ : ℕ) :
    TateOggSaitoTwoAdicData (freyPadicCurve 2 a b) :=
  { v₂Δmin := 4 + 2 * padicValNat 2 (a * b * (a + b))
    m₂ := m₂
    swan₂ := swan₂ }

/-- **Conditional Ogg–Saito landing, general slot records**: for an ABC
triple, if the `v₂Δmin` slot of `d` equals the proved `k = 0` exponent and
the Ogg–Saito relation holds for `f₂`, then `f₂` is the displayed slot
expression.  Both the slot agreement and the relation are hypotheses; no
value of `m₂` or `swan₂` is asserted. -/
theorem freyTwoAdicOggSaitoValue_of_slotData {a b : ℕ}
    (htri : IsABCTriple a b (a + b))
    (d : TateOggSaitoTwoAdicData (freyPadicCurve 2 a b))
    (hΔ : d.v₂Δmin = 4 + 2 * padicValNat 2 (a * b * (a + b)))
    {f₂ : ℕ} (hrel : conductorExponentTwoAdicFormula (freyPadicCurve 2 a b) d f₂) :
    f₂ = 4 + 2 * padicValNat 2 (a * b * (a + b)) + 1 - d.m₂ + d.swan₂ := by
  rw [conductorExponentTwoAdicFormula] at hrel
  rw [hrel, hΔ]

/-- **Conditional Ogg–Saito landing, canonical slots**: same conclusion for
the canonical record `freyTwoAdicAdditiveSaitoSlots`, where the slot
agreement is definitional. -/
theorem freyTwoAdicAdditiveOggSaitoValue {a b : ℕ} (htri : IsABCTriple a b (a + b))
    (m₂ swan₂ : ℕ) {f₂ : ℕ}
    (hrel : conductorExponentTwoAdicFormula (freyPadicCurve 2 a b)
      (freyTwoAdicAdditiveSaitoSlots a b m₂ swan₂) f₂) :
    f₂ = 4 + 2 * padicValNat 2 (a * b * (a + b)) + 1 - m₂ + swan₂ := by
  rw [conductorExponentTwoAdicFormula] at hrel
  simpa only [freyTwoAdicAdditiveSaitoSlots] using hrel

/-- **Placeholder comparison**: on an ABC triple, the placeholder value of
`conductorExponentTwoAdic` coincides with the conditional Ogg–Saito value
exactly when the slot arithmetic returns `2`. -/
theorem freyTwoAdicAdditivePlaceholder_eq_iff {a b : ℕ}
    (htri : IsABCTriple a b (a + b)) (m₂ swan₂ : ℕ) {f₂ : ℕ}
    (hrel : conductorExponentTwoAdicFormula (freyPadicCurve 2 a b)
      (freyTwoAdicAdditiveSaitoSlots a b m₂ swan₂) f₂) :
    (conductorExponentTwoAdic (freyPadicCurve 2 a b) = f₂) ↔
      4 + 2 * padicValNat 2 (a * b * (a + b)) + 1 - m₂ + swan₂ = 2 := by
  have hf := freyTwoAdicAdditiveOggSaitoValue htri m₂ swan₂ hrel
  rw [freyPadicCurve_two_conductorExponentTwoAdic_eq_two a b, hf]
  exact eq_comm

/-- **Exact arithmetic form of the placeholder condition**: the slot
expression returns `2` (with natural truncation) exactly in the two
displayed cases. -/
theorem freyTwoAdicSaitoSlotArithmetic_eq_two_iff (m₂ swan₂ β : ℕ) :
    ((4 + 2 * β + 1 - m₂) + swan₂ = 2) ↔
      (swan₂ ≤ 2 ∧ m₂ = 3 + 2 * β + swan₂) ∨ (swan₂ = 2 ∧ 5 + 2 * β < m₂) := by
  omega

end LeanFormal.IUT
