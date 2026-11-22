# C9 q-pilot donor audit (2026-10-23)

- Task: audit production actual q-pilot object/region/log-volume donors; exact donors or no-go.
- Owner: logdescent.
- Lean target changes: none.
- Conclusion: actual q-pilot **Real log readout** exists; actual q-pilot **region / normalized log-volume** does not. C9 currently uses a hull/C8 readout, not the actual q-pilot donor.

## 1. Actual q-pilot Real donors

### 1a. Arithmetic q-candidate log (best source-compatible donor)

File: `LeanFormal/IUT/IUTIII/Corollary312/ArithmeticQPilotLogVolume.lean`

- `qNorm_pos (parameter : FinitePlaceQCandidate place) : 0 < ‖parameter.q‖` (line25);
- `qNorm_lt_one : ‖parameter.q‖ < 1` (line30);
- `localSignedLog (parameter) : ℝ := Real.log ‖parameter.q‖` (line35);
- `localLogMagnitude (parameter) : ℝ := -localSignedLog parameter` (line39);
- `localSignedLog_neg`, `localLogMagnitude_pos`, `unitNormLogDegree_q` (lines42-64);
- conditionally aggregated `selectedLogMagnitude` / `selectedSignedLog` over
  selected places and weights (lines81-135), explicitly conditional.

Exact type: `localSignedLog (parameter : FinitePlaceQCandidate place) : Real`.
This is the actual signed q log for a C3 `FinitePlaceQCandidate`, but it is a
**point value**, not a q-pilot region and not the procession-normalized
q-pilot log-volume.

### 1b. Canonical Tate q-pilot log-volume

File: `LeanFormal/IUT/IUTIII/Corollary312/TateQPilotJComparison.lean`

- `qPilotLogVolume (l : PrimeGeFive) : ℝ := -Real.log ‖q l‖` (line45);
- `tateQPilotLogComparisonPacket : TateQPilotLogComparisonPacket l` (line129);
- packet fields include `qNorm`, `qLogVolume`, `jLogVolume`, and
  `jLogVolume_eq_qLogVolume` (structure line109).

Exact type: `qPilotLogVolume (l : PrimeGeFive) : Real`.
This is the canonical Tate q-parameter at prime `l`, not the C3 source
q-candidate/region and not a source q-pilot region.

### 1c. Arithmetic q-pilot normalization

File: `LeanFormal/IUT/IUTIII/Corollary312/ArithmeticQPilotGlobalNormalization.lean`

- `selectedLowerSignedLog`, `selectedUpperSignedLog` (lines392/397);
- `absoluteDegreeNormalizedLowerSignedLog`, upper counterpart (lines419/424);
- `normalizedLowerSignedLog_neg` (line454).

These are actual *conditional* finite sums over supplied selected places,
parameters and weights; they do not construct the source place family or the
q-pilot region.

File: `LeanFormal/IUT/IUTIII/Corollary312/ArithmeticQPilotBaseChange.lean`

- `localLogMagnitude_map`, `localSignedLog_map`, `qNorm_map`, and the
  selected/power transport lemmas (lines168-234).

These transport actual q-candidate logs along a completion map; no source
q-pilot region/log-volume object is constructed.

## 2. q-pilot region / log-volume: exact no-go

File: `LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/HullDeterminantLogVolumeReduction.lean`

- `HullDeterminantLogVolumeFrozenSpec` (line123) freezes finite identity
  families; the source-side content is explicitly not proved (lines58-95);
- `Cor312ComparisonData` (line517) has `thetaHullLogVolume`, `qPilotLogVolume`,
  `qPilot_mem_ray`, and `qPilotLogVolume_eq` as **input fields**, with the
  comment that the source construction producing them is not proved;
- `cor312ComparisonData_nonempty` (line569) is a consistency witness on a
  scalar model, not the actual source q-pilot region.

No production declaration defines an actual source q-pilot region in the
source IQ/hull carrier, and no production theorem computes its
procession-normalized log-volume from an actual q-object.  This is a no-go,
not a local proof gap.

Search evidence: no `QPilotRegion`, `qPilotLogVolume` (source IQ), or
actual q-pilot-region declaration under `LeanFormal/IUT` other than the
Tate/arithmetic point values above and the frozen card.

## 3. C9 audit consequence

Current C9 (`SourcePilotApproximationIQ.lean`) defines:

- `Values` from `muLogAt` (C8 signed hull log), not from a q-pilot donor;
- `degreeAt` from `iqDegreeAt` (C8 degree), not from
  `ArithmeticQPilotLogVolume.localSignedLog` / `qPilotLogVolume`;
- `actual_q_approximated` quantifies the C8 degree, not the actual source q.

Therefore the current C9 q-pilot region is wrong: it has no actual q-pilot
region or source q-pilot log-volume object.  The best actual replacement for
the q scalar is `ArithmeticQPilotLogVolume.localSignedLog (C3.q)` (or its
magnitude), with `TateQPilotJComparison.qPilotLogVolume` only as a canonical
Tate comparison; the region/log-volume itself is exact no-go.

## 4. Donor choice

- Actual q scalar: use `ArithmeticQPilotLogVolume.localSignedLog (C3.q)`;
  it is constructed from the same `FinitePlaceQCandidate` as C3.
- Canonical Tate comparison: `TateQPilotJComparison.qPilotLogVolume`,
  `tateQPilotLogComparisonPacket`; not the source q.
- q-pilot region/normalized log-volume: no actual donor; only frozen
  `Cor312ComparisonData` input card / scalar consistency witness.

No Lean target is changed by this audit.