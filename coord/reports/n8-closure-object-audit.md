# N8 closure object audit

Date: 2026-11-06. Scope: tmp/sheaf/n8/closure. Static audit: sorry/axiom counts by `Get-ChildItem` + Select-String, source SHA16.

## Target objects

| Object | Defining file | SHA16 | sorry | axiom | Status |
|---|---|---|---|---|---|
| P6BridgeDonors | C6ConstructedOutput.lean:48 | 7B339DC76CE188D8 | 0 | 0 | structure actual (also variant P6Bridge.lean:52, sorry=3) |
| SourceLogKummerData | SourceLogKummerRealization.lean:47 | D03BEF8B5D117621 | 0 | 0 | structure actual; C2Actual.lean has sorry=2 |
| SourcePilotRegionData | SourcePilotRegion.lean:59 | 237AC890F51119AE | 1 | 0 | structure actual but file has 1 sorry; C3Actual.lean sorry=2 |
| SourceWitnessedOutputData | SourceWitnessedOutput.lean:90 | 97311E15C7B38FE5 | 0 | 0 | structure actual; C4ActualOutputFromSource sorry=0 |
| SourceThetaIQInterface | SourceThetaToIQ.lean:64 | E2D57DD3BDC7C4B0 | 1 | 0 | structure actual but file has 1 sorry; C6ActualIQData sorry=0 |
| C6ActualIQData | C6ActualIQData.lean:32 | 8F76571F273C0AB4 | 0 | 0 | actual; IsActual in C6ActualIdentification.lean sorry=0 |

## Other touched files

- C6ActualIdentification.lean: 64350809C1566090 sorry=0 axiom=0.
- C2Actual.lean: 837FEA0934042E95 sorry=2.
- C3Actual.lean: 8D9115071C54DCE9 sorry=2.
- T11Actual.lean: 9D9C168C44B05E16 sorry=2.

## Consumers (file counts via grep)

- P6BridgeDonors: 22 files; C1Components/C1ContractAttempt/C1DonorCanonical/C1FromP6Donors/C1NativeConsumerPaperRoute/C1P6DonorsFromContract/C1SourceDegree*/C4IndAction*/C4Obligation*.
- SourceLogKummerData: 49 files; C2Actual/C2Native/C5Actual/C5APTProof/C5Native/C5SHEIntegration/C6C7C8NamedClosure ...
- SourcePilotRegionData: 79 files; C3Actual/C3CompleteSourceReduction/C3PilotRoots/C3QPacketIdentificationAttempt/C3T11NamedClosure/C4IQAlignment/C5Actual ...
- SourceWitnessedOutputData: 97 files; C4ExistenceAttempt/C4IndAction*/C4IQAlignment/C4Obligation/C4OldCarrierIndAction ...
- SourceThetaIQInterface: 45 files; C4IQAlignment/C6C7C8NamedClosure/C6ConstructedOutput/C6NormalizationProof/C6PaperInput/C7* ...
- C6ActualIQData: 62 files; C6ActualIdentification/C6ActualIQData/_testc6* ...

## Findings

1. All six target *structure definitions* exist as real Lean objects, not opaque/skeleton Props.
2. P6BridgeDonors, SourceLogKummerData, SourceWitnessedOutputData, C6ActualIQData defining files have 0 sorry.
3. SourcePilotRegionData (SourcePilotRegion.lean) and SourceThetaIQInterface (SourceThetaToIQ.lean) defining files each contain 1 sorry; actual consumers C3Actual/C2Actual/T11Actual also have sorry.
4. No axiom declarations in the six defining files.

## Caveat

This is a static sorry/axiom audit, not kernel/olean/axioms verification. It does not establish that the structures are inhabited or that consumers are closed. A separate serial `#print axioms` pass is required.

