# Independent review: PaperP6NormalizedTarget source/normalization semantics

Date: 2026-10-25
Reviewer: transport
Mode: read-only review. No Lean edits, no proof changes.

## Reviewed artifacts

| file | lines | SHA256 |
|---|---:|---|
| tmp/sheaf/n8/closure/PaperP6NormalizedValuesActual.lean | 78 | 6C7D624C99664B5FDBA9409F530D12EDB425CC7A4C7FCDB4500149DF353EF67A |
| coord/targets/ChallengeNormalized.lean | 15 | 57EB5008A6679B06083CB406020F2A9416F11B35A3E2BF881215323B0996A651 |
| coord/targets/TargetsCheckNormalized.lean | 19 | 80424E58DC45CED5080B2EF767D2C365B14E5D9B3A9442E0261708FA09CD8B57 |

Target:

    normalizedTheta S := thetaLogVolume S / d S
    normalizedValue S T :=
      Real.log ((c6UnitRefNormalizedData ... T).toReal) / d S
    normalizedValueSet S :=
      {z | exists T in allQPilotRegions S, z = normalizedValue S T}

    PaperP6NormalizedTarget S :=
      (forall z in normalizedValueSet S, z <= normalizedTheta S) ∧
      Real.log ||qUnit S|| <= normalizedTheta S

## Verdict

source_semantics_review = PARTIAL

The new target is a genuine degree-normalization correction:
- both value and Theta are divided by the actual local degree d;
- Q is actually in the normalized value set via QPaperNorm_actual;
- the values are still actual q-pilot regions, not arbitrary Real;
- the frozen snapshot is proved by an actual theorem with no sorry.

The remaining issue is the missing identification with C6/C9
normalizedLogVolume: the file defines its own normalizedValue/normalizedTheta
and does not prove they equal C6.normalizedLogVolume / C9 normalized volumes.
The definitions are mathematically consistent, but the normalization bridge is
not formalized in the target.

## (1) Is normalizedTheta = thetaLogVolume/d consistent with the C6/C9 1/d normalizedLogVolume?

Status: CONSISTENT IN FORM, NORMALIZATION BRIDGE NOT PROVED.

C6 normalizedLogVolume is:

    arithmeticTupleNormalizedLogVolume places tuple mu S
      = (1 / (finrank Qp (Block)))
          * (Real.log (mu S).toReal
             - Real.log (mu (canonicalUnitReference)).toReal)

The target defines:

    normalizedValue T =
      Real.log ((c6UnitRefNormalizedData ... T).toReal) / d
    normalizedTheta =
      thetaLogVolume / d

Since c6UnitRefNormalizedData is the actual unit-reference normalized measure,
the intended identity is:

    normalizedValue T
      = C6.normalizedLogVolume T

and similarly for the hull.  This follows from the definitions of the
unit-reference normalized measure and arithmeticTupleNormalizedLogVolume,
together with log laws and positive finite unit-reference mass.

However, this equality is not a declaration in the reviewed file.  The target
uses a new normalizedValue/normalizedTheta pair and only relies on the
definition of c6UnitRefNormalizedData; it does not state or prove:

    normalizedValue T = C6.normalizedLogVolume T
    normalizedTheta = C6.normalizedLogVolume (c6Hull)

Therefore, at the current declaration surface, consistency with C6/C9
normalizedLogVolume is a mathematical expectation, not a proved bridge.

This is the exact remaining normalization lemma:

    normalizedValue_eq_normalizedLogVolume :
      normalizedValue S T = C6.normalizedLogVolume T

    normalizedTheta_eq_normalizedLogVolume_hull :
      normalizedTheta S = C6.normalizedLogVolume (c6Hull)

with C6 taken to be the actual C6ActualIQData and with the same places/tuple/mu.

## (2) qLog_mem_normalizedValueSet via QPaperNorm_actual

Status: ACTUAL.

- qPilotRegion is qUnit * Integers, with qUnit from ClauseB qParameter at the
  chosen lifted bad place.
- qPilotRegion is in allQPilotRegions: qUnit has norm < 1.
- qLog_mem_normalizedValueSet rewrites the normalized value of qPilotRegion
  using QPaperNorm_actual:
      Real.log (qPilot mass) / d = Real.log ||qUnit||.
- Thus the actual paper qLog belongs to normalizedValueSet.

So Q is indeed in the values set, via the actual QPaperNorm_actual theorem,
not by an arbitrary membership assumption.

Caveat: this is the PaperP6 qUnit, not C9Paper.QPaper with C3 provenance.
The C9 QPaper equality remains a separate bridge gap.

## (3) No circularity / arbitrary?

Status: NO circularity, no arbitrary Real.

- PaperP6NormalizedValuesActual imports PaperAllQPilotRegions,
  C7MassFormulaZeroSorry, PaperP6ComparisonActual; none assumes the new target.
- normalizedValueSet is built from actual q-pilot regions q * Integers for
  actual units q with ||q|| <= 1.
- normalizedValue is the actual normalized C6 mass log divided by actual d.
- normalizedTheta is actual thetaLogVolume divided by actual d.
- TargetsCheckNormalized proves the frozen challenge by the actual
  paperP6NormalizedTarget_actual theorem, no sorry in the reviewed source.
- qLog_mem_normalizedValueSet uses the actual QPaperNorm_actual.

No hidden arbitrary Real or target assumption.

## (4) Remaining normalization / semantic gaps

1. Normalization bridge to C6/C9 normalizedLogVolume (main gap):
   the target has its own normalizedValue/normalizedTheta, but no theorem
   identifies them with C6.normalizedLogVolume / C9 normalized volumes.

2. ValuesPaper provenance:
   normalizedValueSet still ranges over all q-pilot regions with norm <= 1,
   not over the paper ValuesPaper provenance / actual source-output family.
   This is narrower than hull-universal, but still broader than the paper
   values family.

3. C9 provenance:
   C9Paper.QPaper.qPilotLogVolume = localSignedLog C3.q is not proved equal to
   PaperP6's log||qUnit||; ThetaPaper.thetaLogVolume =
   C6.normalizedLogVolume (thetaToC6 thetaHull) is not proved equal to
   normalizedTheta.  The exact volume bridge remains C9VolumeBridge /
   C9BridgeGap.

4. Locality:
   Q, Theta and normalizedValueSet are one-factor C6 quantities at the chosen
   bad place; full paper product / actual theta image is not constructed.

5. Division edge:
   normalizedValue/normalizedTheta divide by d.  d is positive in the actual
   development, so this is mathematically safe; the target's inequality proof
   uses nonnegativity of d.  No zero-division issue is hidden, but the target
   does not expose a 0 < d field in its conclusion; it is supplied by the
   actual d_pos theorem globally.

## Final assessment

- normalizedTheta = thetaLogVolume/d: consistent in form with C6/C9 1/d
  normalization, but the equality to C6.normalizedLogVolume is NOT proved in
  the target.
- Q in normalizedValueSet via QPaperNorm_actual: YES, actual.
- No circularity/arbitrary: YES, none.
- Normalization/semantic gaps: normalization bridge, ValuesPaper provenance,
  C9 provenance, locality.

source_semantics_review = PARTIAL.

The target is a valid actual degree-normalized q-pilot-values P6 assembly.  It
is not yet a full C6/C9 normalizedLogVolume statement until the
normalizedValue/normalizedTheta equalities and the C9 provenance bridge are
added.
