# S1179: actual source Kummer isomorphism sources

Date: 2026-10-30. Scope: TimesMuKummer.Isomorphism, SourceKummerArrow,
Kummer theory/root data, and the construction path through actual source links.

## 1. Actual algebraic layer

`LeanFormal/IUT/IUTII/Kummer/TimesMuIsm.lean`

- `TimesMuKummer.Isomorphism source target` (:156): actual structure with
  - `equiv : TimesMuQuotient U ≃* TimesMuQuotient W`;
  - `equivariant : ∀ g x, equiv (action source g x) = action target g (equiv x)`;
  - `invariantImage : ∀ H, equiv '' invariantImage source H = invariantImage target H`;
- `refl`, `precompose`, `orbitOf`, `Ism`, `precompose` action: actual category/orbit
  laws.

This is an actual **algebraic** Kummer-isomorphism layer, but every
`Isomorphism` already requires its source/target group actions as input.

`SourceKummerEvaluationArrows.lean`

- `SourceKummerArrow G upper lower` (:200): actual record with
  `stripIso : FPrimeStripEquiv upper lower` and
  `layer : SourceTimesMuKummerLayer G upper lower`;
- `SourceTimesMuKummerLayer` (:130): actual per-place action/isomorphism data;
- `sourceKummerArrowOfLayer` (:208) actual assembly;
- `sourceKummerArrow_self` (:227): gate-only witness with trivial actions and
  `Isomorphism.refl`.

## 2. Actual source-data interface

`LeanFormal/IUT/IUTII/Frobenioid/SourceKappaOrbitUnitsActionSupply.lean`

- `KappaOrbitUnitsActionDatum G upper` (:144): exact source-data structure with
  `sourceUnits`, `sourceAction`, `factor`, and
  `kappa : ∀ v, TimesMuKummer.Isomorphism (sourceAction v) ((upper.unitsAction v).comp (factor v))`.
- `suppliedUnitsAction` (:172) is the actual strip-level action supplied by the
  factorization.

The structure is not inhabited by root/Frobenioid data; it is an exact source
interface.

`LeanFormal/IUT/IUTII/Frobenioid/SourceKappaOrbitFactorizationProvider.lean`

- `F.universalKappaOrbitUnitsActionDatum` (:111) is unconditional on the
  canonical product group `(v : V) → F.toDPrimeStrip.Pi v`;
- it is built by `canonicalDatumOfFactorization F.evaluationFactorization`.

Important: this canonical completion uses the **identity representative**
(`TimesMuKummer.Isomorphism.refl`) on the canonical factorization.  It is an
actual inhabitant of the interface, but it is not a nontrivial arithmetic
Kummer isomorphism from root/Frobenioid data.

## 3. Actual construction path that does work

`tmp/sheaf/xif/paper/IPLAPTDataActual.lean`

- `selfKummerLayer envStrip` (:68): actual self layer with
  `sourceAction = targetAction = suppliedUnitsAction` and
  `kummer v := TimesMuKummer.Isomorphism.refl ...`;
- `selfEvaluationUnitPortion` (:80): identity unit-layer;
- `selfKummerArrow`, `selfEvaluationArrow`, `selfKummerEvaluationSquare`,
  `selfKummerEvaluationActual`, `selfIplActual` actual.

`tmp/sheaf/xif/paper/LogKummerCorrespondenceFromSource.lean`

- `actualCoreSelfLayer := selfKummerLayer (I.fPrimeStripAt 1 0)` (:50);
- `actualKummerLayerOf upper lower σ τ` (:62) =
  `SourceTimesMuKummerLayer.conjugate actualCoreSelfLayer σ τ`;
- `actualVerticalKummerLayer`, `actualKummerArrow`, `actualVerticalKummerCard`,
  `actualOneColumnLogKummer` (:84-104) actual;
- `actualIPLKummerLayer`, `actualIPLEvaluationUnit`, `actualIPLData` actual.

This file compiles EXIT=0 (verified locally).  The construction is actual:
it conjugates an actual self Kummer layer along actual `fLinkAt` arrows, so it
produces a `SourceTimesMuKummerLayer` and `SourceKummerArrow` between genuinely
different strips (non-identity `stripIso`).

## 4. What it does NOT construct

The Kummer **content** is still the identity representative:

- `selfKummerLayer.kummer = TimesMuKummer.Isomorphism.refl`;
- after conjugation the quotient isomorphism is the conjugate of the identity;
- no root data, Frobenioid evaluation, or non-identity kappa is used.

So this is an actual self-layer/conjugation path, not the paper's nontrivial
Kummer isomorphism from `O^x(G)` to `O^xmu(A)`.

## 5. Exact first gap

First missing source object:

```text
KappaOrbitUnitsActionDatum G upper
```

with a **non-identity** per-place

```text
kappa v : TimesMuKummer.Isomorphism (sourceAction v)
  ((upper.unitsAction v).comp (factor v))
```

whose `equiv` is the actual Kummer/root-data isomorphism of IUT II,
Definition 4.9(i), and whose invariant-image law is nontrivial.

Equivalently, the exact missing sublemma is:

```text
actualSourceKummerIsomorphism :
  ∀ v, TimesMuKummer.Isomorphism
    (actualSourceUnitsAction v)
    ((upper.unitsAction v).comp (actualFactorization v))
```

with actual source units/action/factorization, not the canonical identity
completion.  The current `universalKappaOrbitUnitsActionDatum` proves only the
canonical/identity inhabitant.

## 6. Consumer path

The actual `SourceKummerArrow` produced by
`actualKummerLayerOf`/`actualKummerArrow` is consumed by

- `ThetaLinkIPLFactorizationActual.actualLeftKummer`/`actualRightKummer`;
- `actualSquare` (`SourceKummerEvaluationSquare.ofThreeLegs`);
- `actualThetaLinkSquareData` and the adjacent Kummer-square exchange.

These compile and use the actual fLinkAt/conjugation data.  Replacing the
identity self layer by the nontrivial `actualSourceKummerIsomorphism` above
would upgrade the same consumers to the paper's arithmetic Kummer arrow;
no consumer changes are needed.

## Verdict

- actual: `TimesMuKummer.Isomorphism` structure/category, `SourceKummerArrow`,
  `KappaOrbitUnitsActionDatum` interface, self layer, conjugation along
  `fLinkAt`, actual Kummer arrows/squares (EXIT=0).
- exact first gap: a nontrivial `KappaOrbitUnitsActionDatum.kappa` from actual
  source units/root/Frobenioid data, replacing the canonical identity
  completion.
- no new wrapper; all statements above point to existing actual declarations.
