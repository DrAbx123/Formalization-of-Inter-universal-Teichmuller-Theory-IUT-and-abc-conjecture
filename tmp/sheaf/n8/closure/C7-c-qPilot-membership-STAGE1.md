# C7-c stage 1: q-pilot membership donor

Node: C7-c (child of C7)
Parent: C7 SourceHolomorphicHull
Stage: 1 (statement/route only; no Lean file, no compile)
Date: 2026-10-23
Owner: kummer
Consumers: C7 qPilot_mem

## Exact target statement

    theorem c7_qPilot_mem_canonicalHull :
        SourceThetaToIQ.qPilotPoint (I := I) C3 in
          arithmeticTupleCanonicalHull C3.tensorPlaces C3.tensorTuple

Equivalently, using the actual C6 bridge:

    SourceThetaToIQ.qPilotPoint C3 in
      (C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple mu).hull.

## Exact reductions already available

- SourceThetaToIQ.qPilotPoint C3 =
    C3.tensorLanding (C3.q.q : CommonPrimeCompletion ...) (definition).
- C3.tensorLanding_q :
    C3.tensorLanding (C3.q.q : CommonPrimeCompletion ...) =
      (C3.tensorUnit : ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple).
- SourceThetaToIQ.qPilotPoint_eq_tensorUnit : qPilotPoint C3 = C3.tensorUnit.

Thus the target reduces to

    (C3.tensorUnit : ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)
      in arithmeticTupleCanonicalHull C3.tensorPlaces C3.tensorTuple.

## Why current C3/C6 data are insufficient

C3.tensorUnit is a unit of the arithmetic tensor tuple block. The canonical hull
arithmeticTupleCanonicalHull is the pullback of the canonical lambda-O hull
region; it is not automatically the whole unit group of the tensor ring. No
donor currently states that an arbitrary C3.tensorUnit lies in the canonical
hull. The canonical hull is a bounded/compact region, while the unit group of
the tensor block is generally unbounded.

Therefore this is an exact source-integrality gap: the C3 q-unit must be a
source theta/integral unit whose tensor landing lies in the chosen hull region.

## Required donor / bridge (exact gap)

At least one of:

1. C3 source integrality:
     tensorUnit_mem_canonicalUnitReference :
       (C3.tensorUnit : ArithmeticTensorTupleBlock ...) in
         arithmeticTupleCanonicalUnitReference C3.tensorPlaces C3.tensorTuple
   plus the canonical unit-reference/canonical-hull inclusion or scaling
   relation (paper lambda-O hull with lambda from source normalization); or
2. A direct source q-pilot theorem
     tensorUnit_mem_canonicalHull :
       (C3.tensorUnit : ArithmeticTensorTupleBlock ...) in
         arithmeticTupleCanonicalHull C3.tensorPlaces C3.tensorTuple.

Option 1 is preferred: it exposes the actual integral/unit condition. If lambda
is not 1, C7 needs the scaled region, not the unscaled canonical hull, so the
statement must be adjusted to the actual lambda-O region.

## Proof route once donor exists

1. Rewrite qPilotPoint to C3.tensorUnit via qPilotPoint_eq_tensorUnit.
2. Apply the new tensorUnit_mem_canonicalUnitReference.
3. Use the canonical hull/unit-reference scaling theorem from
   FinitePlaceCompactHullScaling to land in arithmeticTupleCanonicalHull
   (or in the actual lambda-O scaled region if source lambda differs from 1).

## Acceptance

- statement_compiles for C7-c;
- proof_body_checked once the C3 integrality donor is available;
- no free qPilot membership field and no qPilot definition by choice.

## Forbidden substitutions

- Do not define qPilotPoint as a free C7 field.
- Do not replace qPilot by an arbitrary tensorUnit power without C3 proof.
- Do not assume tensorUnit in the hull as an input.
