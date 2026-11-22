# C10 interface checklist (N8 stage 2)

Status: read-only interface audit. No Lean file is written or changed. C10 assembly remains blocked.

First blocker: C5 stage-2 file is red, so there is no actual SourceAlgorithmCompatibilityData
to pass. C0 N8TargetInput/N8TargetOutput are now actual (green, one named sorry); the C0
definitions are usable as C10 input/output types. A C10 file written before C5 is green would
still require fake C5 placeholders, which are forbidden.

C6 update (lead report): PaperNormalizedVolume.lean is green (exit 0, 1 named sorry).
C5 is still red; root cause reported as an import-prefix error, fix in progress by iplsheapt.

## Exact C0-C9 interfaces inspected

| Node | Actual declaration | Parameters / dependency shape | Current status |
|---|---|---|---|
| C0 | N8TargetInput / N8TargetOutput | input I : OriginalInput; output place/realization/hull_finite/hull_positive/qPilot_mem_hull/q_le_theta | GREEN (lead report: exit0, 1 named sorry; actual fields) |
| C1 | SourceInputBinding I | I : OriginalInput l V; field place : SourcePlaceRealization I | green olean exists |
| C2 | SourceLogKummerData I C1 | I, C1 : SourceInputBinding I; finite-place donor fields | green olean exists |
| C3 | SourcePilotRegionData I | I; actual q/theta/tensor/root-change fields; one named sorry | green (exit 0, 1 sorry) |
| C4 | SourceWitnessedOutputData I Label | I, Label, [Group Label]; place/pilot/IndActionData | green olean exists |
| C5 | SourceAlgorithmCompatibilityData I C1 C2 C3 C4 | C4 over Multiplicative LAdd; ipl/she/apt/correspondence | RED |
| C6 | PaperNormalizedVolumeData iota | [Fintype iota]; localVolume/lambdaData/tupleWeights/procession/globalVolume | GREEN (lead report: exit0, 1 named sorry) |
| C7 | SourceHolomorphicHullData D C5 C6 n x | C7-local C5PermittedFamilyData and C6ProductVolumeData | source exists; interface not aligned with actual C5 |
| C8 | sourceDegreeComparison | C6 PaperNormalizedVolumeData, C6Prod, C7 hull; one named sorry | source exists; not compiled |
| C9 | C9SourceConstruction I | C9-local OriginalInput, C2/C3/C5/C8 interface structures | source exists; not actual C1-C8 types |

## Exact C5 blocker

File tmp/sheaf/n8/closure/SourceAlgorithmCompatibility.lean fails with:

- LinkSpan unknown identifier (line 38);
- CardIPLTransportSupply unknown identifier (line 39);
- KummerEvaluationFactor unknown identifier (line 40);
- FPrimeStripEquiv (I.fPrimeStripAt 0 0) supplied where FPrimeStripLink expected (line 48);
- consequent IPLRepresentation / LAdd errors.

Until C5 is repaired, C10 cannot consume SourceAlgorithmCompatibilityData.

## Additional C0 output provenance check

C0 N8TargetOutput.realization requires an actual SourceTheorem311Realization. The current
C1-C9 stage-2 types inspected do not expose that field: C4 has place/pilot/IndActionData,
C5 has IPL/SHE/APT algorithm records, C6-C9 have volume/hull/degree/values. C0's
n8_targetOutput_nonempty is a named obligation, not an allowed C10 input. C10 therefore
needs an explicit source-realization provider (from C5/APT or a separate accepted interface)
before it can fill the C0 output. If C5 does not supply it, the realization field is the
next exact blocker after C5 goes green.

## Interface mismatches beyond C5

1. C7 does not consume the C5 actual type. SourceHolomorphicHull.lean defines its own
   C5PermittedFamilyData (l) (permitted signed labels) and C6ProductVolumeData (Y)
   (product/measure data). C10 would need an explicit transport from
   SourceAlgorithmCompatibilityData to C5PermittedFamilyData, which is not present.
2. C9 does not consume actual C1-C8 types. SourcePilotApproximation.lean defines its own
   OriginalInput (l V), C2SourceLogKummerRealization, C3SourcePilotRegion,
   C5SourceAlgorithmCompatibility, and C8SourceDegreeComparison. These are C9-local
   interface structures, not SourceInputBinding/SourceLogKummerData/SourcePilotRegionData/
   SourceAlgorithmCompatibilityData/C8 actual declarations.
3. C6 requires actual places, tuple, mu, measurable/Borel/add-Haar data, and a
   normalization degree; these are not fields of C1/C2/C3. C10 must receive them as explicit
   C6 construction parameters, not choose them freely.
4. C8 sourceDegreeComparison requires C6/C7 actual data and module imports with
   tmp.sheaf... names; these imports are not yet validated in the closure path.
5. C10 codomain is the C0 stage-2 output type; it is not defined.

## What C10 can be written against once green

A non-fake C10 stage-2 file needs all of the following exact parameters:

- I : OriginalInput l V;
- C1 : SourceInputBinding I;
- C2 : SourceLogKummerData I C1;
- C3 : SourcePilotRegionData I;
- Label and C4 : SourceWitnessedOutputData I Label;
- LAdd with [AddGroup LAdd] and C5 : SourceAlgorithmCompatibilityData I C1 C2 C3 C4
  where C4 must be over Multiplicative LAdd;
- C6 actual data: places/tuple/mu/measurable/Borel/add-Haar plus PaperNormalizedVolumeData
  (or the final C6 type) for those data;
- C7 actual hull data, with a defined bridge from C5 to C5PermittedFamilyData;
- C8 actual degree comparison;
- C9 actual Values/approximation data over the same C2/C3/C5/C8;
- C0 stage-2 output type as codomain.

C10 must not take ipl/she/apt : Prop, q_le_hull, degree_preserved, hq, free
possibleImage, arbitrary tensor/volume data, or any C0 existence theorem.

## Next action

Wait for:
1. iplsheapt to repair C5 (exact errors above);
2. qside to define the C0 stage-2 output type;
3. C7/C9 interface alignment to actual C1-C8 types (or explicit transport bridges).

Then write N8Assembly.lean with the exact parameters above and report first blocker if any
mismatch remains. No empty structures/True/free conclusion placeholders.
