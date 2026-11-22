# S1209: concrete stagePlace attempt / exact first gap

Date: 2026-10-30. No weak interface.

## Attempt

Read actualOneColumnFinitePrimePlace and concreteInput for V = FinitePrimePlace 2 7.

Actual facts:
* concreteInput l : SourceProcessionBoundary.Input with V = FinitePrimePlace 2 7,
  Label = finiteLabel l, Choice = ProcessionChoice l;
* actualOneColumnFinitePrimePlace : SourceOneColumnArithmeticHolomorphicStructure
  (FinitePrimePlace 2 7), with concrete local fields/rings via
  finitePrimePlaceToQ : FinitePrimePlace 2 7 -> NumberField.FinitePlace Q;
* FStageCapsule.source : Fin (n+1) -> I.family.index; strip : FPrimeStrip V.

## Why no stagePlace

concreteInput is a SourceProcessionBoundary.Input, not an OriginalInput.  It has
no family.index and no FStageCapsule; its Choice is ProcessionChoice l
(finiteLabel l × finiteLabel l × Nat), not a finite-prime-place type.  Its
theater/history/carrier fields do not contain a map Fin (n+1) -> FinitePrimePlace.

actualOneColumnFinitePrimePlace fixes the place type V but supplies no assignment
of stage indices to places, and is not connected to concreteInput's Choice,
theater, or history.  FStageCapsule exists only on an OriginalInput, so it cannot
be instantiated from concreteInput.

Therefore there is no function

  stagePlace : Fin (n+1) -> FinitePrimePlace 2 7

and no statement to prove against FStageCapsule.source/strip; trying to build one
by Classical.choice over places would be arbitrary and not source-faithful.

## Exact first sublemma

Construct a genuine source instance I : OriginalInput l (FinitePrimePlace 2 7)
with its family index/stage, plus a source place assignment

  stagePlace : Fin (n+1) -> FinitePrimePlace 2 7

and prove stagePlace is read by the same source capsule strip
(FStageCapsule.source/strip).  Alternatively provide an actual bridge from
concreteInput to such an OriginalInput.  Neither exists in the tree.

## Consumer

SourceHDDReadout (dsc -> hull + det) / Step 3.11.5 SHE q-vs-hull.  The first
sublemma would remove the consumer's stagePlace/local-field identity assumption.

Stopped at this exact first gap; no compatible/isActual/holds Prop, no Nonempty
gate, no weak target.
