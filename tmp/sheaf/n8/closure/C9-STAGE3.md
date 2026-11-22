# C9 stage 3: actual q-pilot readout and exact no-go

Date: 2026-10-23
Owner: transport
Files: `tmp/sheaf/n8/closure/C9Actual.lean`, this record.
Status: C9Actual exit 0; C9 stage-2 theorem remains open/no-go. No `sorry` in C9Actual.

## Actual q-pilot Real readout (defined, compiled)

`C9Actual.lean`:

```lean
noncomputable def actualQPilotRealReadout : ℝ :=
  -Real.log ‖(C3.q.q : CommonPrimeCompletion
      (K := I.initial.arithmetic.Fmod) C3.place)‖
```

This is the actual source q value from C3, not a free Real field.
`actualQPilotRealReadout_eq` is `rfl`.

## Why the C8 signed-hull donor identity is not available

C8's current IQ readouts are independent of `n` and of `C3.q`:

- `C8IQ.iqHullLogVolume` uses `commonHull (C3:=C3) mu B`, and C7 defines
  `commonHull B := B.hull`; it is the canonical hull of `B`.
- `C8IQ.iqSignedHullLogAt` is `B.signedHullLog`.
- `C6ActualIQData.signedHullLog = arithmeticTupleCanonicalHullHaarLog` is
  `Real.log (mu canonicalHull).toReal`.
- No field of `SourcePilotRegionData C3`, `SourceHolomorphicHullData`,
  `C6ActualIQData`, or C8 relates `C3.q.q`'s norm to the canonical-hull
  Haar log.  `SourcePilotRegionData` only records `tensorLanding_q`
  (q lands at the tensor unit), not a hull-volume identity.

Therefore the required donor identity

```
actualQPilotRealReadout C3 = B.signedHullLog
```

is not derivable from the current actual data.  It is not a missing algebraic
manipulation; the bridge object/value does not exist in the interface.

## Why `sourcePilotApproximationIQ_stage2` is no-go as an actual q comparison

C9IQ defines:

```
muLogAt n = iqSignedHullLogAt ... (H := C7 n) = B.signedHullLog
degreeAt n = iqDegreeAt ... (H := C7 n) = B.normalizedLogVolume (B.hull)
Values = range (fun n => muLogAt n) = {B.signedHullLog}
```

Thus `Values` is a singleton constant and contains no q-pilot value.
It does not implement the stage-1 intended `Values(I)` from the actual output
data, and its `actual_q_approximated` mentions `degreeAt` only, not
`actualQPilotRealReadout C3`.

Moreover the approximation inequality is not derivable from the current C8
normalization identity.  Stage 2 now has:

```
iqDegree = B.normalizationWeight * (B.signedHullLog - B.unitReferenceLog)
```

while `Values = {B.signedHullLog}`.  For `epsilon > 0`,
`actual_q_approximated` needs some value `y = B.signedHullLog` with

```
B.normalizationWeight * (B.signedHullLog - B.unitReferenceLog) - epsilon
  <= B.signedHullLog
```

i.e. essentially `B.normalizedLogVolume B.hull <= B.signedHullLog`
(plus `epsilon`).  Nothing in C6/C7/C8 proves this: C7 supplies
`logVolume_pos` for the ENNReal interface log-volume, not a sign or bound on
`B.unitReferenceLog`; `C6ActualIQData.unitReferenceLog` is an unconstrained
Real field (or `log mu unitRef` for the actual value, with no proved sign).

So the stage-2 theorem cannot be closed by a zero-sorry proof from the current
actual interfaces; the missing statements are:

1. actual q-hull donor identity/inequality
   `actualQPilotRealReadout C3 <= B.signedHullLog` (or equality);
2. a normalization/unit-reference inequality
   `B.normalizedLogVolume B.hull <= B.signedHullLog` (or the exact
   C9 sign convention);
3. a replacement of the constant `Values` by the actual output-value set
   from C4/C5/C8, containing the q readout.

## C9Actual theorem status

- `C9Actual.lean`: exit 0, no sorry.
- `actualQPilotRealReadout`: actual definition, compiled.
- `sourcePilotApproximationIQ_stage2`: not proved here; exact no-go as an
  actual q comparison.
- C9IQ stage-2 named sorry remains (not touched).
