# C3 stage 3: actual SourcePilotRegionData

Date: 2026-10-23
Owner: kummer
File: tmp/sheaf/n8/closure/C3Actual.lean
Status: stage 3 constructor + exact no-go record
Verification: lake env lean -R D:/lean tmp/sheaf/n8/closure/C3Actual.lean exit 0, zero sorry.

## Constructed object

SourcePilotRegionDonors records the exact actual donor fields required by the
frozen C3 stage-2 structure:

- p : Nat with [Fact p.Prime];
- place : FinitePlaceAtPrime I.initial.arithmetic.Fmod p;
- q : FinitePlaceQCandidate place.val  (not Real q);
- thetaPacket : FiniteThetaPacket l;
- roots, roots' : NatRootSystem (candidateUnits place q);
- kummerClass, rootChange : CyclotomicTower (CommonPrimeCompletion place);
- rootChange_eq : rootChange = KummerClass.rootSystemDiff roots roots';
- tensorIndex, tensorFintype, tensorPlaceIndex, tensorPlaces, tensorTuple;
- tensorUnit : (ArithmeticTensorTupleBlock tensorPlaces tensorTuple)^x;
- tensorLanding : CommonPrimeCompletion place -> ArithmeticTensorTupleBlock ...;
- tensorLanding_q : tensorLanding q.q = tensorUnit.

The actual constructor is

sourcePilotRegionDataOfDonors : SourcePilotRegionDonors I -> SourcePilotRegionData I

It sets qUnit := candidateUnits place q by definition and fills every C3 field
from the donor record.  No Real surrogate for q and no free conclusion fields
are used.

The zero-sorry conditional existence theorem is

sourcePilotRegion_nonempty_of_donors :
  SourcePilotRegionDonors I -> Nonempty (SourcePilotRegionData.{...,0,0} I).

It is currently stated at tensor universes 0 for the tensorIndex/tensorPlaceIndex
types; the donor structure itself contains the exact data.

## Exact no-go for the unconditional statement

The unconditional theorem

  sourcePilotRegion_nonempty (I : OriginalInput) : Nonempty (SourcePilotRegionData I)

is not derivable from OriginalInput alone.  OriginalInput contains only:

- initial : SourceDefinition31Data l, whose arithmetic data contains fields
  Fmod/F/K and a tower/curve but no selected rational prime p;
- family/index plus prime strips;
- compatibility Propositions.

It does NOT contain:

1. a selected rational prime p and a finite place at p;
2. a q in the completion (all source q data are Real-valued; there is no
   Real -> CommonPrimeCompletion map in the tree, the A1 obstruction);
3. two actual NatRootSystem structures for the q unit;
4. an actual Kummer class/root-change tower;
5. a finite tensor index, tensor places, tensor tuple, tensor unit, or a
   completion -> arithmetic tensor landing map.

The frozen SourcePilotRegionData structure requires all of these as fields, so
an unconditional inhabitant cannot be constructed without new source donors.
The exact first missing donor is the actual finite-place q in the completion.
This file therefore proves the conditional constructor and records the no-go;
it does not introduce an axiom, a fake q, or a Real-valued substitute.

## Consumers

- C5 SourceAlgorithmCompatibilityData (C3 parameter).
- C4 SourceWitnessedOutputData / C7 SourceHolomorphicHullData (C3 tensor data
  and q).
- C8/C10 downstream after C3 donors are supplied.

## Next executable step

Supply SourcePilotRegionDonors from C1/C2/C3 source data, starting with:

1. C3-d1: selected p and FinitePlaceAtPrime (from C1 place realization);
2. C3-d2: actual q in CommonPrimeCompletion, with q.q_ne_zero;
3. C3-d3: thetaPacket from the actual theater theta packet;
4. C3-d4: roots/rootChange from the actual Kummer class;
5. C3-d5: tensor index/places/unit/landing from the arithmetic tensor tuple.

Until C3-d1/C3-d2 are supplied, sourcePilotRegion_nonempty remains an exact
no-go, not a proved theorem.
