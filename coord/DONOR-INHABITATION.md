# DONOR-INHABITATION — C1/C2/C3 source-donor search (read-only)

Status: READ-ONLY inventory, 2026-11-12. No files outside this doc/coord were modified.
Purpose: determine whether the C1/C2/C3 donors needed by QPilotIdentificationActual have
actual inhabitants, and if not, list the exact constructor parameters.

## 1. Search results

C1ActualData:
- type/structure: tmp/sheaf/n8/closure/C1Actual.lean:38
- conditional constructor: sourceInputBindingOfActual (:60), sourceInputBinding_nonempty_of_actual (:66)
- native constructor: C1ActualDataNative.lean:31 c1ActualDataOfNativeDonors
- C6 constructor: C1ActualDataC6.lean:40 c1ActualDataOfC6Supplies
- component wrapper: C1Components.lean:27 C1ActualDataComponents; constructors
  c1ActualDataOfComponents (:34), ofBinding (:67)
- P6 donor constructor: C1FromP6Donors.lean:35 / C1DonorCanonical.lean:35
  (Nonempty C1ActualData from P6BridgeDonors / NativeOldBindingDonorsExist)
- packet constructor: NativeC1PaperSource.lean:86 c1ActualData (inside a
  NativeC1PaperSource packet); sourceInputBinding (:90)
No literal instance of the form "instance : C1ActualData" and no explicit construction
outside these conditional constructors was found. All C1ActualData inhabitants are
conditional on a donor record.

SourcePilotRegionDonors:
- type: tmp/sheaf/n8/closure/C3Actual.lean:44; constructor sourcePilotRegionDataOfDonors
  (:79); nonempty sourcePilotRegion_nonempty_of_donors (:105).
- S1408 constructor: tmp/sheaf/xif/paper/S1408C3LSourcePilotConsumerActual.lean:116
  sourcePilotRegionDonorsOfLBlock
    (D : SourcePilotRegionDataL (I := I))
    (B : SourcePilotOldCompletionBlock (I := I) D) :
    SourcePilotRegionDonors (l := l) (V := FinitePrimePlace 2 7) I.
  The block B is SourcePilotOldCompletionBlock = CompletionRootBlock at the L core;
  S1408 proves Nonempty B iff Nonempty (NatRootSystem D.qUnit), and B is an input,
  never inhabited there.
- C3ActualThetaPacketWitnessConstruction.lean:71 can replace only thetaPacket given a
  donor D; it does not build the root/Kummer block.
- ConcreteC3DonorAssemblyActual.lean:126 records the remaining fields for a full donor.
No unconditional SourcePilotRegionDonors inhabitant found.

NativeC1PaperSource:
- structure: tmp/sheaf/n8/closure/NativeC1PaperSource.lean:51
- fields: X : N8NativeInput l; S : NativeSourceAssembly X.S;
  e : X.family.index = SourceTheorem311Index; R : NativeImageRealizationSourceFields X
  (assemblyInput X S e); F : NativeFiberSourceFields X (assemblyInput X S e)
  (nativePlaceIndexEquiv X).
- derived: c1ActualData (:86), sourceInputBinding (:90), packet_outputs (:113);
  NativeC1PaperSourceExists (:120) is exactly Nonempty (NativeC1PaperSource l).
- no literal instance of NativeC1PaperSource was found. The only uses are as a parameter
  (NativeOneColumnActual:24, QPilotLineActualConstruction:19, S366OneColumnActual:15).
  So the packet is an explicit source input, not an available instance.

## 2. C1 verdict — NO actual inhabitant, conditional constructors exist

- SourceInputBinding I is constructed by sourceInputBindingOfActual I D from
  D : C1ActualData I; C1ActualData has four fields:
  placeEquiv : V = NumberFieldPlaceIndex; selected : V;
  selected_realization : I.SourceImageRealization selected;
  fiberMonEquiv : forall n m v, (I.primeStripAt n m).Mon v = SourcePlaceValueGroup ... .
- Native/C6/P6 constructors take larger donor records:
  NativeOriginalInputDonors + NativePlaceBindingDonors, P6BridgeDonors /
  NativeOldBindingDonorsExist, C6ContractSupply + index equivalence, or the five-field
  NativeC1PaperSource packet.
- Verdict: C1 has no actual instance in the tree; it is conditional on a donor record.
  The smallest concrete parameter is NativeC1PaperSource l (five fields above). Once such
  a packet is supplied, P.c1ActualData and P.sourceInputBinding are green.

## 3. C2 verdict — constructor green, conditional only on C1

- C2Actual.lean:32 sourceLogKummerDataActual (I) (C1 : SourceInputBinding I) :
  SourceLogKummerData I C1; theorem sourceLogKummerData_nonempty_actual (:58).
- This is a complete actual construction from C1, using sourceLocalLogShellDatum and the
  actual unit-log kernel/log-shell identities; no additional donor.
- Verdict: C2 has no standalone instance but needs only C1; if C1 is supplied, C2 is
  green and unconditional relative to C1.

## 4. C3 verdict — NO actual inhabitant; requires completion root block or full donors

- SourcePilotRegionData I is built by sourcePilotRegionDataOfDonors D from
  D : SourcePilotRegionDonors I (19 fields: p, place, q, thetaPacket, roots, roots',
  kummerClass, rootChange, rootChange_eq, tensorIndex/fintype/placeIndex/places/tuple/
  unit/landing/landing_q).
- S1408 gives the closest actual reduction:
  sourcePilotRegionDonorsOfLBlock D B, with
  D : SourcePilotRegionDataL (actual L pilot; S1391 has actualSourcePilotRegionDataL
  for the concrete place) and B : CompletionRootBlock (the exact old completion root/
  Kummer block). S1408 proves Nonempty B iff Nonempty (NatRootSystem D.qUnit) and
  actual... iff completionFirstFieldObstruction; B is not inhabited.
- S1408 also constructs oldSourcePilotOfLBlock D B : SourcePilotRegionData from the same
  data, so once B is supplied the whole C3 record is available.
- Verdict: C3 has no actual instance; constructor is green conditional on
  SourcePilotRegionDataL + CompletionRootBlock (S1408), or on the full 19-field donor
  record. The exact missing first field is the old completion root system
  (NatRootSystem (concreteQUnit ...)), not a Lean error.

## 5. Summary table for abc

| stage | actual inhabitant? | constructor / parameter | green status |
|---|---|---|---|
| C1 | NO | sourceInputBindingOfActual (C1ActualData) or NativeC1PaperSource packet (X,S,e,R,F) | constructors green; no instance |
| C2 | NO standalone, only on C1 | sourceLogKummerDataActual (C1) | green conditional only on C1 |
| C3 | NO | sourcePilotRegionDonorsOfLBlock (L pilot, CompletionRootBlock) or 19-field donors | green conditional; completion root missing |
| oneColumn | actual for V=FinitePlace k | sourceOneColumnStructureOfNumberField k | green |
| strip | constructor needs FPrimeStrip | SourceFTimesMuPrimeStrip.canonical F | green conditional on F |
| qPilotIdentificationActual | NO | qPilotIdentificationActualOfCanonical L F oneColumn | green assembler, no inhabitant |

Recommended handoff to abc: supply a NativeC1PaperSource l packet (or the equivalent
NativeOldBindingDonorsExist/P6BridgeDonors) to get C1; C2 follows automatically. For C3,
either supply the S1408 completion root block together with the actual L pilot
(SourcePilotRegionDataL), or the full SourcePilotRegionDonors record. Until then,
QPilotIdentificationActual remains a source-donor obligation, not a compiled gap.
