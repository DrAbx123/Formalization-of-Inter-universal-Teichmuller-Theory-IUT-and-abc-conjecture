# S227: tensor hull and L field-unit hull Haar transport

Date: 2026-10-29. Object-first; no inequality.

## Actual transport

tensorBlockMeasurableSpace is transported from L via the S214 linear
equivalence; tensorHaarTransport is the pushforward of the actual L Haar under
the inverse equivalence.

tensorLambdaOHull = S214 tensorThetaHullPreimage.
LFieldUnitHull = S214 LThetaClosureHull.

tensorBlockLinearEquiv maps tensorLambdaOHull exactly onto LFieldUnitHull.

## Measure relation

tensorHaarTransport_preimage proves that for every measurable S in L,
the transported Haar of the CLE-preimage equals the L Haar of S.

tensorHaarTransport_tensorLambdaOHull_eq proves the exact hull measure relation

  tensorHaarTransport tensorLambdaOHull
    = rootNormedHaar LFieldUnitHull.

LFieldUnitHull_measurable proves the L hull is measurable (finite theta image).

## Object

TensorHullHaarLogData packages the actual tensor Haar, tensor hull, L Haar,
L hull, both hull logs, and the hull log relation; tensorHullHaarLogData is the
actual instance.  The exact measure relation is proved above.

No fake Haar/log/sorry/axiom/True/PUnit; no inequality.
