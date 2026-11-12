# SourceDegreeHullC3 conditional-interface audit

Date: 2026-10-28. Scope: read-only audit of tmp/sheaf/n8/closure/SourceDegreeHullC3.lean plus the required header note and this report. No DAG, STATE, AUDIT_LEDGER, or other files edited.

## 0. Verdict

SourceDegreeHullC3.lean is a conditional interface. C6, C6Prod, and C7 are variables in all three exported theorems. No actual PaperNormalizedVolumeData, C6ProductVolumeData, or SourceHolomorphicHullData instance is constructed or passed here. The three importers are probes/gates that either #check or #print axioms these conditional theorems; none supplies actual C6/C6Prod/C7 inhabitants.

The header note was added:

    Conditional interface: C6/C6Prod/C7 are variables; no actual PaperNormalizedVolumeData/C6ProductVolumeData instance is constructed here.

No theorem was changed.

## 1. Readers/importers of SourceDegreeHullC3.lean

Searched tmp/sheaf/n8/closure for "SourceDegreeHullC3" and for the exact import line. Three readers found:

| reader | import line | use |
|---|---:|---|
| tmp/sheaf/n8/closure/C1SourceDegreeGate.lean | 4 | imports; #check's sourceDegreeResidual_iff_actualDegree_eq_BHull_c3 (line 18) and sourceDegreeHullReadoutIdentification_c3 (line 20) |
| tmp/sheaf/n8/closure/probes/ProbeHullC3.lean | 1 | imports; #print axioms c8HullLogVolume_c3_eq_normalizedLogVolume (line 2) |
| tmp/sheaf/n8/closure/probes/ProbeHullC3Unconditional.lean | 1 | imports; #print axioms sourceDegreeHullReadoutIdentification_c3 and sourceDegreeResidual_iff_actualDegree_eq_BHull_c3 (lines 2-3) |

No other import of SourceDegreeHullC3 was found in tmp/sheaf/n8/closure.

## 2. Search evidence for actual constructors/inhabitants

Search roots: D:\lean\LeanFormal and D:\lean\tmp (the only trees containing project Lean files). The three target type names occur zero times in LeanFormal; all occurrences are in tmp/sheaf/n8/closure.

### PaperNormalizedVolumeData

Definition: tmp/sheaf/n8/closure/PaperNormalizedVolume.lean:104, structure PaperNormalizedVolumeData.

Actual constructors/instances: NONE found.
- No "def ... : PaperNormalizedVolumeData" and no "instance ... : PaperNormalizedVolumeData" in tmp/sheaf/n8/closure.
- C6ProductBridge.lean:39 has a field paper : PaperNormalizedVolumeData ...; a field of a bridge structure, not an inhabitant.
- All other occurrences are theorem/definition parameters, variables, or the field accessors (e.g. C8DegreeActual, SourceDegreeComparison, SourceDegreeHullComponents, SourceDegreeHullBridge, SourceDegreeHullC3, SourcePilotApproximation, N8Assembly).
- C6ActualIQData.actual (used in SourceDegreeHullC3) is an actual IQ-data constructor of a different type; it is NOT a PaperNormalizedVolumeData.

### C6ProductVolumeData

Definition: tmp/sheaf/n8/closure/C7Interface.lean:33, structure C6ProductVolumeData (Y).

Actual constructors/instances: NONE found.
- C6ProductBridge.lean:37 is "structure C6ProductBridge ... extends C6ProductVolumeData"; it is a bridge structure, not an actual C6ProductVolumeData instance.
- C7Interface.lean:45-50 attribute [instance] registers fields of the structure for instance search; it does not construct an inhabitant.
- All other occurrences are variables/parameters (N8Assembly, SourceDegreeActualDegreeBridge, SourceDegreeComparison, SourceDegreeComponents, SourceDegreeHullBridge, SourceDegreeHullC3, SourceDegreeHullComponents, SourcePilotApproximation).

### SourceHolomorphicHullData

Definition: tmp/sheaf/n8/closure/SourceHolomorphicHull.lean:77, structure SourceHolomorphicHullData.

Actual constructors/instances: NONE unconditional.
- C7Actual.lean:69 defines SourceHolomorphicHullData.ofObligations from an explicit C7ActualObligations argument. This is a conditional constructor, not an actual inhabitant.
- C7Actual.lean:103-107 proves Nonempty SourceHolomorphicHullData iff Nonempty C7ActualObligations; still conditional on the obligations.
- All other occurrences are variables, parameters, or conditional Nonempty statements (C7Native, C7HullPackagePaperRoute, C7QPilotTargetCorrection, C7ThetaMembershipDecisive, SourceDegreeComparison, SourceDegreeComparisonIQ, SourceDegreeHullBridge, SourceDegreeHullC3, SourceDegreeHullComponents, SourcePilotApproximationIQ, N8Closure, N8PaperObligations, etc.).
- No def/instance supplies an actual SourceHolomorphicHullData on C3.tensorPlaces/C3.tensorTuple/muIQ.

## 3. C3-specific evidence

In SourceDegreeHullC3.lean:
- line 37: (C3 : SourcePilotRegionData ...)
- line 47: {C6Prod : C6ProductVolumeData (Y := I.ThetaPilotPoint D.place.v)}
- line 50: (C6 : PaperNormalizedVolumeData C3.tensorPlaces C3.tensorTuple muIQ)
- line 51: (C7 : SourceHolomorphicHullData ... mu := muIQ ...)
- lines 68, 81 repeat C6 and C7 as theorem parameters.

Thus all C3-instantiated hull-readout theorems consume C6/C6Prod/C7 as hypotheses. No actual C6/C6Prod/C7 term is supplied in this file or by its three readers.

The actual C3 tensor block and C6ActualIQData.actual are real project data, but they do not provide PaperNormalizedVolumeData, C6ProductVolumeData, or SourceHolomorphicHullData.

## 4. Header note and compile

Header note added to SourceDegreeHullC3.lean immediately after the existing module description:

    Conditional interface: C6/C6Prod/C7 are variables; no actual PaperNormalizedVolumeData/C6ProductVolumeData instance is constructed here.

No theorem statement or proof was changed. File hash after edit:

    tmp/sheaf/n8/closure/SourceDegreeHullC3.lean
    lines: 107
    SHA256: C4C7E1C8CD4ACC9CD4D2ACF2E8137F97E13C49F8B3BB4722B7F5F53FFA152B45

Compilation command:

    cd D:\lean
    lake env lean -j1 -R 'D:\lean' -o '.lake\build\lib\lean\tmp\sheaf\n8\closure\SourceDegreeHullC3.olean' 'tmp\sheaf\n8\closure\SourceDegreeHullC3.lean' 2>&1

Result: EXIT 0. No output beyond the exit marker.

## 5. Exact status

- SourceDegreeHullC3.lean is a conditional interface over C6/C6Prod/C7 variables.
- No actual PaperNormalizedVolumeData instance exists in the searched tree.
- No actual C6ProductVolumeData instance exists in the searched tree.
- No unconditional actual SourceHolomorphicHullData exists; only the conditional ofObligations constructor and conditional Nonempty statements.
- Its three readers are gates/probes and do not supply actual inhabitants.
- The file compiles (EXIT 0) with the added header note.
- No DAG, STATE, AUDIT_LEDGER, or non-write-path file was edited.
