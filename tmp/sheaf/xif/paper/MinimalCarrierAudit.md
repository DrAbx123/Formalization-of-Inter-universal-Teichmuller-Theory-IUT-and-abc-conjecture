# Minimal carrier audit: xi-f scalar consumption

Question: does the paper-level xi-f scalar need only the per-b tensor block, or
does it need the product hull carrier / canonical tuple block?

Answer: for the scalar consumed by the paper-level sum, only the per-b
one-factor tensor block is required. The product hull carrier and the canonical
tuple block are not needed for the scalar and are removed from the critical
path. No coherence map is required because the product carrier is not used.

## 1. Actual scalar shape

The scalar is the finite weighted sum over bad places:

  globalQVFamThetaHullLog
    = sum over b of nativeBadLocalWeight b * localThetaHullLog b.

Each localThetaHullLog is defined on the one-factor tensor block

  qVFamTensorBlock T b

with:

- qVFamTensorPlaces T b, qVFamTensorTuple;
- the actual fractional lattice coefficient from qVFamily;
- qVFamLambdaOHull = qVFamQPilotRegion T b;
- arithmeticTupleNormalizedLogVolume on that same block.

The weight nativeBadLocalWeight is a finite real weight. No product of local
fields is taken by the scalar consumer.

## 2. Product hull carrier

QVFamThetaHullActual uses the product carrier

  (b : Bad) -> Multiplicative Real

and builds qVFamilyThetaImagePoint, qVFamilyThetaProductImageSet, and
qVFamilyThetaHull. That object is useful for an image-set hull audit on the
product value carrier, but the xi-f scalar above never consumes it.

Consequences:

- no actual coherence map from the product carrier to the per-b tensor blocks
  is required;
- if one wanted to use the product hull scalar, one would need an actual map
  from product points to local tensor points and a compatibility theorem for
  the log-volume. That map is absent and is not introduced here.
- the product hull file is removed from the minimal scalar path. It had no Lean
  consumer.

## 3. Canonical tuple block

The canonical tuple block (arithmeticTupleCanonicalHull / canonical unit
reference) is actual and useful for a different Haar-normalization audit.
It is not the per-b qVFamily tensor block and is not used by the scalar sum.
The earlier canonical Haar ratio was therefore an unnecessary carrier for this
scalar. It is removed from QVFamScalarPrerequisitesActual.

## 4. What the minimal per-b carrier still needs

The per-b block scalar still needs actual fields that are not supplied by the
coefficient data:

1. actual local unit Haar positivity and finiteness;
2. actual local theta-hull Haar positivity and finiteness;
3. actual equality of the local normalized log-volume with the paper
   procession average (or an equivalent normalized mono-analytic log-volume
   identity);
4. actual tensor image-point alignment/landing, if the scalar is to be
   identified with the image hull rather than only with the fractional scaled
   region.

These are recorded as exact gaps in QVFamScalarPrerequisitesActual:
QVFamLocalNormalizationGap and its required proposition.

No product-hull coherence map, no canonical tuple-block comparison, no
LGP/Kummer/Ind, and no fake inclusion is added.
