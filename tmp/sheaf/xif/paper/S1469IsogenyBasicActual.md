# S1469: minimal actual TauCeti-style isogeny base structure

Date: 2026-10-31. EXIT=0; olean generated.

## Source read

TauCeti AlgebraicGeometry/EllipticCurve/Isogeny/Basic.lean:
* CoordinatePullback W1 W2 := W2.CoordinateRing -> W1.FunctionField (F-alg hom);
* Isogeny W1 W2 fields: pullback, mapsInfinity;
* mapsInfinity is integrality of source coordinate ring over target coordinate ring;
* degree and fieldPullback are later TauCeti files (FunctionField/Degree), not in Basic.

## Current v4.32.2 actual base structure (standalone)

The file uses Mathlib's WeierstrassCurve.Affine CoordinateRing/FunctionField
(import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point) and defines:

  CoordinatePullback W1 W2 := W2.CoordinateRing ->ₐ[F] W1.FunctionField
  MapsInfinity pullback :=
    letI := pullback.toRingHom.toAlgebra
    forall x : W1.CoordinateRing,
      algebraMap W1.CoordinateRing W1.FunctionField x
        in integralClosure W2.CoordinateRing W1.FunctionField
  structure Isogeny W1 W2 where
    pullback : CoordinatePullback W1 W2
    mapsInfinity : MapsInfinity pullback
    fieldPullback : W2.FunctionField ->ₐ[F] W1.FunctionField
    fieldPullback_algebraMap : forall x,
      fieldPullback (algebraMap W2.CoordinateRing W2.FunctionField x) = pullback x
    degree : Nat

These are actual data fields, not True/Prop placeholders. No inhabitant of
Isogeny is asserted; the identity isogeny's mapsInfinity proof is not copied
from TauCeti (TauCeti is not a dependency of this project). First exact
inhabitant would require constructing a concrete pullback and its mapsInfinity
and fieldPullback/degree data.

## Use

S1465-S1467 consumers can take phi : S1469IsogenyBasicActual.Isogeny W1 W2
and use phi.pullback, phi.fieldPullback, phi.degree.

## Verification

EXIT=0; olean path
.lake/build/lib/lean/tmp/sheaf/xif/paper/S1469IsogenyBasicActual.olean.
