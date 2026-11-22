# S2732 — object sufficiency gate: six objects

Date: 2026-11-07. Audit only. A carrier is SUFFICIENT only if it contains a
coordinate for every prime in `arithmeticPrimeSupport (abcRationalPoint a c)`
and can compute `arithmeticWeight` on that support. Otherwise INSUFFICIENT.

## 1. ArithmeticLineBundleActual

Verdict: INSUFFICIENT for full prime support / hweightvol.

- It constructs the actual UNIT fractional ideal `1` of `O_K` and its
  O-module, localization, determinant, and global log-volume.
- A unit ideal has empty finite support: `FractionalIdeal` of `1` cannot carry
  the q-pilot ideal/line-bundle data or the ABC support.
- The file itself marks the missing source field
  `PaperQPilotLineBundleSource.qPilot_lineBundle_identification`.
- It is actual as a unit-bundle layer, but NOT a support-complete q-pilot
  arithmetic line bundle.

Completion standard: construct an actual q-pilot fractional ideal/line bundle
with a support dictionary, prove localization at every finite place, and prove
the determinant/global log-volume agrees with the support/weight dictionary.

## 2. S2717Cor312FullTargetActual

Verdict: INSUFFICIENT as an object for paper 3.12; CONDITIONAL numeric target.

- Corrected hupper now uses actual `paperQAbsLog fiveLabel logQ` (S2691), not
  `exp(-theta)`.
- But `S2717ThetaHullLogVolume` is the S2711 concrete signed hull log-volume,
  not a support-complete global theta hull, and `S2717UpperGap` is an explicit
  hypothesis field.
- As a statement it is honest; as a closing object it is insufficient.

Completion standard: construct the actual global theta hull on the support
product and PROVE `S2717UpperGap`, not carry it as a hypothesis.

## 3. S2721BridgeSkeletonActual

Verdict: INSUFFICIENT / false hweightvol for the fixed-scale bridge.

- `S2586IQHullLogVolumeInterface` has `scaleShift := id`; the region is
  `unitRegion ∪ {point}`, and the point is measure-zero.
- S2730HweightvolCounterexampleActual refutes that fixed-scale hweightvol.
- S2721 is a skeleton with explicit gaps, not a final carrier.

Completion standard: replace the fixed `scaleShift` by an actual point-dependent
λ-object and prove the region-volume scaling formula.

## 4. S2727GlobalQVFamHullActual

Verdict: ACTUAL but INSUFFICIENT for hweightvol (bad-only).

- Carrier is `QVFamProductCarrier T` indexed by
  `Bad (nativePlaceSelection T)` only.
- `arithmeticWeight` needs the full rational prime support; bad places do not
  contain it.
- Therefore S2727 is not the final hweightvol carrier.

Completion standard: a support-complete global product carrier (bad places plus
finite support) with arithmeticWeight dictionary and actual region volume.

## 5. S2730PointScalingComparisonActual

Verdict: INSUFFICIENT (bad-only carrier; general scaling only conditional).

- Point-dependent region λ(point)·O is the right direction, but the carrier is
  still `QVFamProductCarrier T` (bad-only).
- `S2730GeneralHaarScaling` is an explicit Prop; only prime-p scaling is actual
  (S2730RegionScalingActual).

Completion standard: support-complete carrier + actual general Haar scaling
formula for the paper λ(point), with region volume proof.

## 6. S2731PointScaledHullActual

Verdict: INSUFFICIENT as written; index does not contain support.

- `S2731Carrier := (v : V) -> ThetaPilotPoint v` with only `[Fintype V]`.
- `V` is the abstract OriginalInput family index; no field/proof says it
  contains `arithmeticPrimeSupport (abcRationalPoint a c)`.
- The template (finite support product) is right, but the index is not yet the
  support.

Completion standard: add an explicit finite support `S` with
`arithmeticPrimeSupport (abcRationalPoint a c) ⊆ S`, an injective index
`S -> V` (or `S`-indexed carrier), and a region/weight dictionary using the
same `S`.

## 7. Six-object summary

| # | object | actual? | supports ABC support? | gate |
|---|---|---|---|---|
| 1 | ArithmeticLineBundleActual | actual unit layer | NO (unit ideal is trivial) | INSUFFICIENT |
| 2 | S2717Cor312FullTargetActual | conditional actual | NO | INSUFFICIENT as object |
| 3 | S2721BridgeSkeletonActual | skeleton | NO (fixed scaleShift=id) | INSUFFICIENT |
| 4 | S2727GlobalQVFamHullActual | ACTUAL | NO (bad-only) | INSUFFICIENT for hweightvol |
| 5 | S2730PointScalingComparisonActual | partial/conditional | NO (bad-only) | INSUFFICIENT |
| 6 | S2731PointScaledHullActual | template | NO (abstract V) | INSUFFICIENT |

No object is SUFFICIENT for the final hweightvol/3.12 gate yet.

## 8. Common completion standard

A future object is SUFFICIENT only if it has ALL of:

1. support-complete carrier: an actual map from the full finite support;
2. actual arithmeticWeight dictionary on that support;
3. actual point-dependent λ region (not fixed `scaleShift=id`);
4. actual region-volume/scaling theorem;
5. hweightvol PROVED, not an explicit field;
6. no `sorryAx`/extra axiom; axioms trio.

## 9. ArithmeticLineBundleActual verdict and curveLineBundle API requirement

### ArithmeticLineBundleActual: INSUFFICIENT

It is actual as a UNIT fractional-ideal layer: `unitLineBundle = 1`, the
O_K-module, localizations, determinant, and global log-volume are actual. But:

- the unit ideal has empty finite prime support;
- it is not the q-pilot line bundle;
- its own module header names the missing source identification
  `PaperQPilotLineBundleSource.qPilot_lineBundle_identification`.

Hence it does NOT cover the full prime support. Verdict: INSUFFICIENT for
hweightvol / paper 3.12.

### curveLineBundle: INSUFFICIENT; needs a new API

`SourceQlThetaLineBundleFromCurve.lean` only defines the actual curve, the
infinite-place divisor type/degree, and lists six missing data:

```lean
inductive SourceThetaLineBundleMissingDatum
  | curveLineBundle
  | thetaObjectATheta
  | geometricThetaDivisor
  | unitComparisonMqMTheta
  | muTwoLDeckRootAction
  | conjugateSynchronization
```

The first item `curveLineBundle` is explicitly MISSING: no line bundle on the
actual arithmetic curve, no theta object, no geometric theta divisor, no unit
comparison, no deck action, no conjugate synchronization.

New API required:

1. `CurveLineBundle S : Type` with a rank-one locally-free O-module structure
   on `S.arithmetic.curve`;
2. `thetaObjectATheta` and the theta-divisor witness;
3. `unitComparisonMqMTheta : Mq -> MTheta`;
4. `muTwoLDeckRootAction`;
5. `conjugateSynchronization`;
6. support/localization/degree dictionary compatible with the support-complete
   hweightvol carrier.

Until that API exists, `curveLineBundle` is INSUFFICIENT and cannot be used to
construct the global support-complete region/weight object.

## 10. curveLineBundle vs actual units (Mq/MTheta/mu_2l)

`curveLineBundle` still requires a NEW algebraic-geometry API:

- an actual line bundle on the arithmetic curve `S.arithmetic.curve`,
- theta object `A_Theta`,
- geometric theta divisor with theta structure,
- unit comparison `Mq -> M_Theta`,
- `mu_(2l)` / `l-Z` deck action,
- conjugate synchronization.

However, the unit-side pieces have actual carriers already:

- `sourceThetaObjectIntegralUnits S =
   (NumberField.RingOfIntegers S.arithmetic.F)ˣ` (actual);
- `sourceThetaObjectIntegralUnitLog` and the product-formula normalization are
  actual;
- `sourceThetaObjectDivisorType =
   (NumberField.InfinitePlace S.arithmetic.F -> Int)` (actual);
- `mu_(2l)` can be sought among roots of unity of `O_F^×` using the actual
  unit group (needs an `IsPrimitiveRoot`/2l-torsion construction, not yet in
  this file).

Therefore:

- `curveLineBundle`: INSUFFICIENT, needs new AG API.
- `Mq/MTheta`: candidates can be CONSTRUCTED from the actual integral units
  (and their product-formula normalization), not from a fake line bundle;
  the actual construction/proof is still missing.
- `mu_(2l)`: candidate root-of-unity construction from the actual units is
  possible; needs an explicit `mu_2l` API and proof.

## 11. q-pilot line bundle support requirement

Required condition:

```text
support (q-pilot line bundle / fractional ideal) ⊇ V_bad
```

(and, for the full hweightvol carrier, also the finite ABC support).

- The actual unit line bundle is FAIL: its fractional ideal is `1`, hence its
  finite support is empty, so it cannot contain `V_bad`.
- The q-pilot fractional ideal/line bundle must be a nontrivial actual
  `Ideal O_K` / `FractionalIdeal O_K K` whose prime-support set contains every
  finite place in `V_bad`; the support dictionary must also expose the ABC
  support primes needed by `arithmeticWeight`.
- No fake choice of ideal is allowed; the q-pilot ideal/source identification
  remains the missing datum (`qPilot_lineBundle_identification`).
