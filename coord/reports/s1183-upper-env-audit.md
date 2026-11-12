# S1183: audit of S1180 upperEnv / Kummer layer

Date: 2026-10-30.  Scope: `tmp/sheaf/xif/paper/S1180SourceUpperEnvActual.lean`, its
dependencies `LogKummerCorrespondenceFromSource`, `IPLAPTDataActual`,
`SourceEvaluationUnitPortionConjugation`, and the `SourceKummerEvaluationArrows`
records.  No new Lean object is written.

## Verdict

**S1180's `upperEnv` is not a bare rename of `fLinkAt`; but it is also not an
actual evaluation arrow.**  Its `stripIso` is the generic source link
`I.fLinkAt 1 0 1 1`, and its `unitPortion` is obtained from
`SourceEvaluationUnitPortion.ofKummerLayer` applied to a layer that is the
**conjugate of the identity self Kummer layer**.  The Kummer layer is actual as
a typed record, but its Kummer isomorphism content is `Isomorphism.refl` (the
identity at the supplied action), not the paper's source Kummer isomorphism at
the actual strips.

## Evidence

### 1. S1180 `upperEnv` assembly

`S1180SourceUpperEnvActual.lean:39-44`:

```text
upperEnv = sourceEvaluationArrowOfUnitPortion
  (I.fLinkAt 1 0 1 1)
  (upperEnvUnitPortion)
```

`upperEnvUnitPortion := SourceEvaluationUnitPortion.ofKummerLayer
  (upperEnvKummerLayer)` (`:33-37`).

`upperEnvKummerLayer := actualKummerLayerOf I
  (I.fPrimeStripAt 1 0) (I.fPrimeStripAt 1 1)
  (I.fLinkAt 1 0 1 0) (I.fLinkAt 1 0 1 1)` (`:26-31`).

### 2. `actualKummerLayerOf` is self-layer conjugation

`LogKummerCorrespondenceFromSource.lean:62-67`:

```text
actualKummerLayerOf := SourceTimesMuKummerLayer.conjugate (actualCoreSelfLayer ...) sigma tau
actualCoreSelfLayer := selfKummerLayer (I.fPrimeStripAt 1 0)
```

`IPLAPTDataActual.lean:65-76` defines `selfKummerLayer` with
`sourceAction = targetAction = suppliedUnitsAction` and
`kummer v := TimesMuKummer.Isomorphism.refl (suppliedUnitsAction v)`.

Thus the conjugated layer's `kummer v` is the conjugate of the identity
isomorphism; it transports the identity through the strip links, but supplies
no nontrivial source Kummer isomorphism.  It is actual *as the self record*,
not actual as the paper evaluation/Kummer content.

### 3. `ofKummerLayer` only drops fields

`SourceEvaluationUnitPortionConjugation.lean:109-115`: `ofKummerLayer` is
`sourceAction := L.sourceAction`, `targetAction := L.targetAction`,
`unitLayer := (L.kummer v).equiv`, with equivariance taken from `L.kummer`.
It does not add the source evaluation or operation provenance.  In S1180 the
input layer is the self-identity layer, so the extracted unit portion is the
identity/self portion conjugated along `fLinkAt`.

### 4. The generic fLinkAt side

`upperEnv.stripIso = I.fLinkAt 1 0 1 1` by `upperEnv_stripIso`
(`S1180SourceUpperEnvActual.lean:45-46`).  `I.fLinkAt` is the generic source
F-prime-strip link, and the report
`s1177-source-output-prime-strip-exact-gap.md` explicitly forbids renaming
generic `fLinkAt` to the actual evaluation arrow.  Here the rename is only
partial: it supplies the `stripIso` field, while the `unitPortion` is the
self-identity conjugate.

## Kummer layer audit

`SourceTimesMuKummerLayer` itself is actual data: source/target actions on
`(Mon v)^x` and a `TimesMuKummer.Isomorphism` with invariant-image law
(`SourceKummerEvaluationArrows.lean:130-139`).  However:

* `selfKummerLayer` uses `TimesMuKummer.Isomorphism.refl`; the
  `SourceKummerEvaluationArrows` docstring labels the analogous
  `sourceKummerArrow_self` as a gate-only witness, not the paper Kummer iso
  (`:224-233`).
* `actualKummerLayerOf` has no theorem identifying its `kummer` with the
  actual source Kummer isomorphism; it is only the conjugate of the identity.
* The invariant-image law is therefore the law of the transported identity
  action, not a source Kummer theorem.

So the layer is actual in type/construction, but its arithmetic content is
self/identity; it cannot be cited as the actual Kummer layer in the sense of
IUT II Definition 4.9 or IUT III Theorem 3.11 (ii)/(iii).

## Can upperEnv feed the square consumer?

`SourceEnvColumnArrows.upperEnv` (`SourceOutputPrimeStripInterpretation.lean:96-99`)
is defined as `upperEval.stripIso` of a supplied `SourceEnvColumnArrows`, so the
same caveat applies to the current official file.  Filling its `upperEval` with
S1180's `upperEnv` would place the self-identity-conjugated unit portion in the
evaluation slot; the resulting `envSquareCommutes` would be a square of
transported identity data, not the paper evaluation/Kummer square.

## Exact first gap (unchanged)

The next honest source sublemma is not another wrapper around `fLinkAt` or
`selfKummerLayer`; it is:

```text
actualSourceKummerIsomorphismAt
  (upper lower : FPrimeStrip V) :
  SourceTimesMuKummerLayer G upper lower
```

with `kummer v` equal to the actual source Kummer isomorphism obtained from the
source operation, not `TimesMuKummer.Isomorphism.refl`, and an actual
evaluation operation supplying `upperEnv`.  The report
`s1177-source-output-prime-strip-exact-gap.md` states the same stop point;
S1180 closes only the self-conjugation/type part, not the source arithmetic
content.

## Recommendation

* Do not cite S1180 `upperEnv` as actual evaluation; mark it self-conjugate
  candidate data.
* Keep `actualKummerLayerOf` as a transport constructor, not as the actual
  Kummer layer.
* Reopen only at `actualSourceKummerIsomorphismAt` / actual source evaluation
  operation; no further wrapper/conjugation file is progress.

## S1183 follow-up: field-level audit (upperEnv self-conjugate candidate)

Verification: `lake env lean` on `S1180SourceUpperEnvActual.lean` exits 0.  That
only checks the self-conjugate construction; it does not supply the actual
source Kummer isomorphism.

### Confirmation

`upperEnv` is a **self-conjugate candidate**:

```text
upperEnv.stripIso = I.fLinkAt 1 0 1 1                 -- actual generic link
upperEnv.unitPortion = ofKummerLayer upperEnvKummerLayer
upperEnvKummerLayer = conjugate (selfKummerLayer (I.fPrimeStripAt 1 0)) ...
selfKummerLayer.kummer v = TimesMuKummer.Isomorphism.refl ...
```

It is not the paper evaluation arrow: the Kummer unit layer is the identity
self-layer transported through `fLinkAt`; no source Kummer isomorphism and no
evaluation operation is used.

### What A (actual upperEnv) still needs

A = actual `SourceEvaluationArrow (ActualKummerGroup) upper lower` with
`upper = I.fPrimeStripAt 1 0`, `lower = I.fPrimeStripAt 1 1` requires the
following actual fields, none supplied by S1180:

1. `SourceTimesMuKummerLayer G upper lower` with:

```text
sourceAction : ∀ v : V, G →* MulAut ((upper.Mon v)ˣ)
targetAction : ∀ v : V, G →* MulAut ((lower.Mon v)ˣ)
kummer : ∀ v : V, TimesMuKummer.Isomorphism (sourceAction v) (targetAction v)
```

2. For each `v`, `TimesMuKummer.Isomorphism (sourceAction v) (targetAction v)`
   must have the actual three fields, not `Isomorphism.refl`:

```text
equiv : TimesMuQuotient ((upper.Mon v)ˣ) ≃* TimesMuQuotient ((lower.Mon v)ˣ)
equivariant : ∀ g x,
  equiv (TimesMuQuotient.action (sourceAction v) g x) =
    TimesMuQuotient.action (targetAction v) g (equiv x)
invariantImage : ∀ H,
  equiv '' (TimesMuKummer.invariantImage (sourceAction v) H) =
    TimesMuKummer.invariantImage (targetAction v) H
```

3. An actual evaluation operation supplying
   `stripIso : FPrimeStripEquiv upper lower` as the paper evaluation, not the
   generic `I.fLinkAt 1 0 1 1`; plus the operation-provenance theorem that the
   chosen source evaluation produces this `stripIso` and this `kummer`.

4. For the adjacent `envSquareCommutes`/`SourceKummerEvaluationSquare`, the same
   actual Kummer layer is needed at both vertical edges (left/right), plus the
   actual lower/upper evaluation arrows; otherwise the square only compares
   transported identity data.

### Exact first missing field

The first non-circular missing object is:

```text
actualKummerIsomorphismAt (upper lower : FPrimeStrip V) :
  ∀ v, TimesMuKummer.Isomorphism (actualSourceAction v) (actualTargetAction v)
```

with `equiv` and `invariantImage` coming from the actual source Kummer
isomorphism, not from `TimesMuKummer.Isomorphism.refl` conjugated by
`fLinkAt`.  This is the same stop as `s1177-source-output-prime-strip-exact-gap.md`;
S1180 supplies only the self-conjugate type-level candidate.

