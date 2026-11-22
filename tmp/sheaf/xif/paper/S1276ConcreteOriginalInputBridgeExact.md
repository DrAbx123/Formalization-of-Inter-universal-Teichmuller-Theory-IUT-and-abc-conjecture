# S1276: concrete stagePlace / OriginalInput bridge

Date: 2026-10-30. Exact only; no new wrapper. HDD lattice/Ind untouched.

## Read

S1209ConcreteStagePlaceGapActual/MD and S1218ConcreteInputBridgeGapActual/MD
(plus S1222 family-constructor audit).

## S1209 result

concreteInput l : SourceProcessionBoundary.Input with
V = FinitePrimePlace 2 7, Choice = ProcessionChoice l.  It is not an
OriginalInput; it has a single theater/history and no family.index /
FStageCapsule.  actualOneColumnFinitePrimePlace fixes V but gives no
Fin(n+1) -> FinitePrimePlace assignment.  No stagePlace exists.

## S1218 result

OriginalInput needs:
  initial : SourceDefinition31Data l
  family : SourceHodgeTheaterFamily l (FinitePrimePlace 2 7)
  index_equiv : family.index ≃ Int × Int
  arithmetic_alignment.
concreteInput supplies none of initial/family/index_equiv.

## Attempt at a genuine OriginalInput

1. initial: SourceDefinition31Data.toSource exists only as
   StageConstructionTrace.toSource, requiring T : StageConstructionTrace l.
   No concrete T/SourceDefinition31Data is in the tree.
2. family: the actual finiteIntegralTwoTheaterFamily l has index Bool, so it
   cannot satisfy index_equiv : family.index ≃ Int × Int.
   sourceInitialThetaSpineFamily can build over arbitrary I, but for
   I = Int × Int needs an injective P : Int×Int -> FPrimeStrip and
   E : FPrimeStripLinkSystem P; neither exists.
3. arithmetic_alignment would additionally need a shared arithmetic root
   (Definition31DualContractAlignment-style).

Therefore neither a genuine OriginalInput l (FinitePrimePlace 2 7) nor a
stagePlace : Fin(n+1) -> FinitePrimePlace 2 7 is constructible.

## Exact first field

initial : SourceDefinition31Data l
next: family : SourceHodgeTheaterFamily l (FinitePrimePlace 2 7)
with index ≃ Int × Int, then index_equiv and arithmetic_alignment.

## Consumer

Concrete stageToLocal / SourceHDDReadout (dsc -> hull+det) and its downstream
capsule/tensor consumer.  The bridge would remove the stagePlace/local-field
identity assumption.

No compatible/isActual/holds Prop, no Nonempty gate, no arbitrary place map.
