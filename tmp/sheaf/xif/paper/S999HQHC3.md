# S999: hQ and hC3 exact minimum

Date: 2026-10-30. Exact conditions; no fake.

## Exact hC3

S999LineC3Identification I C3 Oa := Oa.line.C3 = C3.

## Exact hQ

S999QPilotLogVolumeIdentification I C3 :=
  (concreteO I).qPilotLogVolume = paperQPilotLogVolume C3.

## Exact minimum

S999ExactMinimum I C3 Oa := hC3 and hQ.

No inhabitant is asserted; these are exactly S991/S994's inputs.

## From the minimum

s999LinkInputs: hC3 -> hQ -> S983LinkInputs.
s999PaperXiFSourceLink: hC3 -> hQ -> PaperXiFSourceLink (concreteO I) P C3.
s999Minimum_implies_S994Link: S999ExactMinimum -> Nonempty
  (PaperXiFSourceLink (concreteO I) P C3).

The concrete link is exactly S994's s994ConcreteLink input pattern.

## Note

The source-q route ConcreteSourceQIdentification (in
ConcreteQPilotLogIdentificationActual) gives hQ from
O.qPilotLogVolume = paperQPilotLogVolume C3, but its dependency
ConcreteC3DonorActual currently fails compilation (universe errors and sorry
warnings), so this file does not import it.  hQ is therefore kept as the exact
minimum rather than derived from a broken chain.

No equality/scaling proof is fabricated; the two equalities are source/link
identification conditions consumed as exact inputs.
