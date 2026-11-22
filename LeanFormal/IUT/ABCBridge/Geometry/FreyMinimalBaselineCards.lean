import LeanFormal.IUT.ABCBridge.Geometry.FreyTwoAdicCaseTableCards

/-!
# Shape cards for the Frey minimal-model baseline at the prime `2`

This file records the shape of the baseline row for the displayed Frey model
`y * y = x * (x - a) * (x + b)` and its halved model at the prime `2`, as
used by the abc-Frey conductor analysis.  Every field is a slot; no
minimality statement, valuation, or fibre type is asserted or endorsed.

The companion files `FreyConductorTwoAdic` and `FreyTwoAdicMinimalReduction`
record the two-adic facts proved in this repository; the slots here do not
fill their open conductor gap.

Literature freeze: Silverman, *Advanced Topics in the Arithmetic of
Elliptic Curves*, Chapter IV, Section 9 (Tate's algorithm) and Section 10
(the conductor of an elliptic curve); the module `TateOggSaitoTwoAdicCards`
carries the full freeze.
-/

namespace LeanFormal.IUT.ABCBridge.Geometry.FreyMinimalBaselineCards

open LeanFormal.IUT.ABCBridge.Geometry.TateOggSaitoTwoAdicCards
open LeanFormal.IUT.ABCBridge.Geometry.FreyTwoAdicCaseTableCards

/-- Shape-only baseline row for the displayed and halved two-adic models of
an abc-Frey triple.  All entries are slots. -/
structure FreyMinimalBaselineShape (t : AbcFreyTripleShape) where
  /-- Slot: `v_2` of the displayed discriminant. -/
  displayedDiscriminantValuation : ℤ
  /-- Slot: `v_2` of the discriminant of the halving change. -/
  halvedDiscriminantValuation : ℤ
  /-- Slot: minimality statement for the displayed model. -/
  displayedModelIsMinimal : Prop
  /-- Slot: minimality statement for the halved model. -/
  halvedModelIsMinimal : Prop
  /-- Slot: the Kodaira type of the special fibre at `2`. -/
  twoAdicFiber : KodairaFiberTypeShape

/-- Statement shape: every abc-Frey triple datum is assigned a baseline
row. -/
def FreyMinimalBaselineCard (t : AbcFreyTripleShape) : Prop :=
  Nonempty (FreyMinimalBaselineShape t)

end LeanFormal.IUT.ABCBridge.Geometry.FreyMinimalBaselineCards
