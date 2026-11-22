import LeanFormal.IUT.ABCBridge.Geometry.TateOggSaitoTwoAdicCards

/-!
# Shape cards for the `p = 2` case table of the abc-Frey family

This file records the shape of the case table used to organise the two-adic
analysis of an abc-Frey triple `a + b = c`.  Every entry is a slot; the
actual case values (valuations, reduction types, conductor exponents) are
not determined here and are deferred to later, separately verified work.

Literature freeze: Silverman, *Advanced Topics in the Arithmetic of
Elliptic Curves*, Chapter IV, Section 9 (Tate's algorithm) and Section 10
(the conductor of an elliptic curve); the module `TateOggSaitoTwoAdicCards`
carries the full freeze, including the IV.11 placement of Ogg's formula and
the Saito 1988 bibliographic record.
-/

namespace LeanFormal.IUT.ABCBridge.Geometry.FreyTwoAdicCaseTableCards

open LeanFormal.IUT.ABCBridge.Geometry.TateOggSaitoTwoAdicCards

/-- Shape of an integral abc-Frey triple datum `a + b = c`.  Every field is
a slot. -/
structure AbcFreyTripleShape where
  a : ℕ
  b : ℕ
  c : ℕ
  /-- Slot: the sum relation `c = a + b`. -/
  sumSlot : c = a + b
  /-- Slot: pairwise coprimality of the three coordinates. -/
  pairwiseCoprimeSlot : Nat.Coprime a b ∧ Nat.Coprime a c ∧ Nat.Coprime b c
  /-- Slot: non-vanishing of the product. -/
  nonzeroSlot : a * b * c ≠ 0

/-- Shape slot: which of the three coordinates of an abc-Frey triple is
even. -/
inductive EvenCoordinateShape where
  | aEven
  | bEven
  | cEven
deriving DecidableEq, Repr

/-- Statement shape: exactly one of `a`, `b`, `c` is even.  Not asserted
here; a later construction is expected to fill this slot. -/
def ExactlyOneCoordinateEvenShape (t : AbcFreyTripleShape) : Prop :=
  (Even t.a ∧ Odd t.b ∧ Odd t.c) ∨ (Odd t.a ∧ Even t.b ∧ Odd t.c) ∨
    (Odd t.a ∧ Odd t.b ∧ Even t.c)

/-- One row of the `p = 2` case table, indexed by the parity case.  All
entries are slots; no value is endorsed. -/
structure TwoAdicCaseRowShape (k : EvenCoordinateShape) where
  /-- Slot: `v_2` of the even coordinate. -/
  valuationOfEvenCoordinate : ℕ
  /-- Slot: `v_2` of the discriminant of the displayed model. -/
  displayedDiscriminantValuation : ℤ
  /-- Slot: `v_2` of the minimal discriminant. -/
  minimalDiscriminantValuation : ℤ
  /-- Slot: the conductor exponent at `2`. -/
  conductorExponent : ℕ
  /-- Slot: the Kodaira type of the special fibre at `2`. -/
  fiberType : KodairaFiberTypeShape
  /-- Slot: the minimal-model relation attached to this row. -/
  minimalModelRelation : Prop

/-- Statement shape: a `p = 2` case table indexed by the parity case
exists, with all entries as slots. -/
def TwoAdicCaseTableShape : Prop :=
  ∀ k : EvenCoordinateShape, Nonempty (TwoAdicCaseRowShape k)

end LeanFormal.IUT.ABCBridge.Geometry.FreyTwoAdicCaseTableCards
