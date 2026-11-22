# C7-b stage 1: IQ-hull log-volume positivity donor

Node: C7-b (child of C7)
Parent: C7 SourceHolomorphicHull
Stage: 1 (statement/route only; no Lean file, no compile)
Date: 2026-10-23
Owner: kummer
Consumers: C7 logVolume_pos

## Exact target statement

For the actual bridge

    B := C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple mu

the actual IQ-hull log-volume of the canonical hull is positive:

    theorem c7_iqHull_logVolume_pos :
        0 < (C6ActualIQData.actual C3.tensorPlaces
              C3.tensorTuple mu).iqInterface.logVolume
            (C6ActualIQData.actual C3.tensorPlaces
              C3.tensorTuple mu).hull

C7 field form:

    logVolume_pos : 0 < B.iqInterface.logVolume (commonHull ... B).

## Existing exact donors

- FinitePlaceIQHullInterface:
  arithmeticTupleIQHullLogVolumeInterface,
  arithmeticTupleIQHullLogVolumeInterface_hull,
  arithmeticTupleIQHullLogVolumeInterface_logVolume.
- FinitePlaceArithmeticTupleCanonicalHull:
  measure_arithmeticTupleCanonicalRegions_pos_lt_top gives
  0 < mu (arithmeticTupleCanonicalHull) and finiteness.
- SourceHullCompactnessReduction.IQHullLogVolumeInterface:
  unitRegion_logVolume_lt_top and monotonicity; no positivity field.

## Exact obstruction

The actual interface logVolume is the extended Haar log-volume

    logVolume S = haarLogVolume mu S
                = if mu S = top then top
                  else ENNReal.ofReal (Real.log (mu S).toReal).

Thus 0 < logVolume (canonicalHull) is equivalent to

    Real.log (mu (canonicalHull)).toReal > 0,
    i.e. 1 < mu (canonicalHull)

(or the corresponding normalization condition). The available donor only proves
0 < mu (canonicalHull) < top, which is compatible with mu (canonicalHull) < 1
and negative log-volume.

Therefore this is not only a missing proof step: the current normalization
(unit region = canonical hull, scaling = identity, arbitrary additive Haar
measure) does not imply positivity.

## Required donor / bridge (exact gap)

Choose one actual source normalization and prove the comparison:

1. Provide a C6 actual normalization theorem
     one_lt_measure_canonicalHull :
       1 < mu (arithmeticTupleCanonicalHull C3.tensorPlaces C3.tensorTuple)
   under the paper normalization (IUT IV Prop. 1.4(i), C6 responsibility); or
2. Replace the C7 field logVolume_pos by a normalized-volume sign statement
   with the actual normalization unit, e.g. positivity of normalizedLogVolume
   of the hull relative to the canonical unit reference, and prove it from C6.

Option 1 is direct if the source Haar normalization makes the canonical hull
have measure > 1; otherwise C7 must carry the normalized log-volume rather than
raw Haar log-volume.

## Proof route once donor exists

1. Rewrite B.iqInterface.logVolume to haarLogVolume mu
   (arithmeticTupleIQHullLogVolumeInterface_logVolume).
2. Rewrite B.hull to arithmeticTupleCanonicalHull
   (arithmeticTupleIQHullLogVolumeInterface_hull).
3. Prove haarLogVolume_pos_of_one_lt_measure from Mathlib/Real.log and apply
   one_lt_measure_canonicalHull.

## Acceptance

- statement_compiles for normalized statement;
- proof_body_checked once either measure > 1 theorem or normalized positivity
  theorem is available;
- no arbitrary positive-volume field and no 0 < ... assumption.

## Forbidden substitutions

- Do not assume 0 < logVolume hull as a C7 input field.
- Do not take the whole ambient as hull.
- Do not use an arbitrary Haar measure not tied to C6 normalization.
