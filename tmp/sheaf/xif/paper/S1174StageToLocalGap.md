# S1174: stageToLocal exact first gap

Date: 2026-10-30. No weak interface / no chicken object.

## Named consumer

SourceHDDReadout (dsc -> hull + det readout), feeding the Step 3.11.5 /
SHE special-case q-vs-hull comparison.  The concrete consumer path is:

  FStageCapsule/H2FProcession -> actual local fields K_v/O_v
    -> finite log-shell tensor packet -> hull -> determinant readout.

## Responsibility this would eliminate

The consumer currently has to assume a map from a capsule stage to the actual
local completions and tensor packet.  A real stageToLocal construction would
remove that assumption, supplying:

* stagePlace : Fin (n+1) -> V;
* stageLocalField i = Completion (finitePrimePlaceToQ (stagePlace i));
* stageLocalRing i = CompletionIntegers (...);
* compatibility of stagePlace/strip with the actual source family index and
  the FPrimeStrip at that place;
* the induced map to the finite tensor packet.

Then SourceHDDReadout would no longer need stagePlace/local-field/tensor
prerequisites.

## Actual donor audit (typechecked)

* FStageCapsule.source : Fin (n+1) -> I.family.index;
* FStageCapsule.strip i : FPrimeStrip V (no distinguished v : V);
* FStageCapsule.link i j : FPrimeStripEquiv (strip i) (strip j);
* H2FProcession.canonical supplies stages/inclusions, but no local fields;
* actualOneColumnFinitePrimePlace is a Card AS instance only at
  V = FinitePrimePlace 2 7;
* finitePrimePlaceToQ : FinitePrimePlace 2 7 -> NumberField.FinitePlace Q;
* Card AS/AV/SL reduced; tensor/hull realization exists only for an abstract
  finite family A, not for a capsule stage.

## First gap

There is no map

  stagePlace : Fin (n+1) -> V

and no proof that the capsule's source index/strip is the same actual source
local object as the completion K_v/O_v at such a place.  The stage carries
only I.family.index + FPrimeStrip V; V is a parameter and the stage has no
chosen place.  actualOneColumnFinitePrimePlace fixes V=FinitePrimePlace 2 7
but is not connected to I.family.index or to FStageCapsule.source/strip.

Hence stageToLocal cannot be constructed without adding an unproved source
identification; doing so via an arbitrary Classical.choice map would be a
chicken bridge.  Stopping at this exact first gap.

## No new object

S1174StageToLocalGapActual.lean only typechecks the donors; it does not create a
weak stageToLocal/isActual/holds structure or a Nonempty gate.
