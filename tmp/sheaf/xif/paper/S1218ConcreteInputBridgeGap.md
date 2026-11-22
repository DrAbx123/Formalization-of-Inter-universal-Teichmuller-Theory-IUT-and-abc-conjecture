# S1218: concreteInput -> OriginalInput bridge attempt / exact first field

Date: 2026-10-30. No weak interface.

## Attempt

Read SourceProcessionBoundary.Input/concreteInput and OriginalInput.

Input (concreteInput l) has:
* theater : HodgeTheater;
* history : HodgeTheaterHistory;
* carrier : Carrier Label Choice with Label = finiteLabel l,
  Choice = ProcessionChoice l (finite labels × finite labels × Nat);
* baseChoice/packetVolume/target_q/route_normal_form.

OriginalInput l V has:
* initial : SourceDefinition31Data l;
* family : SourceHodgeTheaterFamily l V, with index ≃ SourceTheorem311Index
  (Int × Int), injective distinct theaters, link/refl/symm/trans laws,
  permutation + permutationLink + naturality;
* arithmetic_alignment.

## Why no direct bridge

concreteInput is a SourceProcessionBoundary.Input, not an OriginalInput.  It
contains a single theater/history, not an Int × Int-indexed family of distinct
theaters with links and permutation data; its Choice is ProcessionChoice, not
the family index.  Constructing a singleton family does not work because
index_equiv requires family.index ≃ Int × Int and distinct requires an
injective theater map on that index.

FStageCapsule.source/strip are only defined on an OriginalInput, so concreteInput
cannot supply a stagePlace : Fin (n+1) -> FinitePrimePlace 2 7 either.  A constant
place map (e.g. to 2) would be arbitrary and not source-faithful.

## Exact first field

The first missing field of an OriginalInput bridge is

  initial : SourceDefinition31Data l.

No SourceDefinition31Data instance is available from concreteInput (it has only
HodgeTheater.arithmetic : InitialThetaArithmeticData, not the full Definition
3.1 contract: selected/bad places, reduction, torsion, orbicurve, sections,
cusp, four compatibility Props and proofs).

Even after initial, the next missing field is

  family : SourceHodgeTheaterFamily l (FinitePrimePlace 2 7)

with its Int × Int index, distinct theaters, links and permutation, which
concreteInput does not provide.  Then index_equiv and arithmetic_alignment.

## Consumer

SourceHDDReadout (dsc -> hull + det) / Step 3.11.5 SHE q-vs-hull; the bridge
would give FStageCapsule/stagePlace data.  Stopped at initial/family; no
compatible/isActual/holds Prop, no Nonempty gate, no weak target.
