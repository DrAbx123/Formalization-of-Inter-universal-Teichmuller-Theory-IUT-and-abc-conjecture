# S1181: non-refl TimesMuKummer.Isomorphism between actual strips

Scope: determine whether an actual non-refl `TimesMuKummer.Isomorphism`
between `I.fPrimeStripAt 1 0` and `I.fPrimeStripAt 1 1` exists, from actual
source units action / quotient / Kummer data.  No weak Lean.

## Search result

Actual / reusable declarations:

- `TimesMuKummer.Isomorphism.refl` (`TimesMuIsm.lean:179`): only identity;
- `TimesMuKummer.Isomorphism.precompose`, `sourceDifference`, `orbitOf`;
- `SourceEvaluationUnitPortion.ofKummerLayer` (`:109`): extracts a unit
  portion from a `SourceTimesMuKummerLayer`;
- `SourceSHETransportConjugation` `conjugate`: transports a given isomorphism;
  conjugating `refl` still yields a refl-shaped isomorphism;
- `KappaOrbitUnitsActionPairDatum.layerKummer`
  (`SourceKappaOrbitUnitsActionSupply.lean:375`): an actual non-refl composite
  `kappaUpper.equiv.symm.trans kappaLower.equiv` between the two strip units
  actions;
- `FPrimeStrip.universalKappaOrbitUnitsActionDatum`
  (`SourceKappaOrbitFactorizationProvider.lean:111`): canonical single-strip
  datum; its `kappa` is `TimesMuKummer.Isomorphism.refl` (see
  `canonicalDatumOfFactorization`, `:310-318`).

Missing: no inhabitant of `KappaOrbitUnitsActionPairDatum` for actual
`upper = I.fPrimeStripAt 1 0`, `lower = I.fPrimeStripAt 1 1` exists.  There is
also no direct construction of a non-refl `TimesMuKummer.Isomorphism` from
`FPrimeStripEquiv` alone in the current tree.  `S1180.upperEnv` is built from
`selfEvaluationUnitPortion` / conjugation, hence is refl/conjugated-refl, not
an actual evaluation.

## First missing source arithmetic object

### Object

```text
KappaOrbitUnitsActionPairDatum G upper lower
```

for the actual strips upper/lower, over one common group-theoretic module:

```text
sourceUnits : V → Type
sourceAction : ∀ v, G →* MulAut (sourceUnits v)
factorUpper : ∀ v, G →* upper.Pi v
factorLower : ∀ v, G →* lower.Pi v
kappaUpper : ∀ v, TimesMuKummer.Isomorphism (sourceAction v)
  (upper.unitsAction v ∘ factorUpper v)
kappaLower : ∀ v, TimesMuKummer.Isomorphism (sourceAction v)
  (lower.unitsAction v ∘ factorLower v)
```

The needed non-refl content is `kappaLower` (or `kappaUpper`): an
`Ism`-orbit representative of the `O^{x mu}(G) ~> O^{x mu}(A_v)` isomorphism,
not `refl` and not a conjugated `refl`.

### Quantifier

```text
for every actual source input I : OriginalInput l V,
for every place v : V,
for the strip pair upper = I.fPrimeStripAt 1 0, lower = I.fPrimeStripAt 1 1.
```

### Consumer

```text
KappaOrbitUnitsActionPairDatum.layerKummer
  -> SourceTimesMuKummerLayer G upper lower
  -> SourceEvaluationUnitPortion.ofKummerLayer
  -> S1180 upperEnv unitPortion
  -> SourceEvaluationArrow upperEnv
  -> upperEnv slot / commEnv of SourceFTimesMuPrimeStripRem3102Diagram
  -> iplLink / iplAlgorithmicProvenanceCard.
```

## Why no new Lean object is written

Any Lean `def` here would either

- assume the missing `KappaOrbitUnitsActionPairDatum` (the exact gap), or
- reuse `selfEvaluationUnitPortion`/`conjugate`, i.e. refl-shaped data, which
  the task forbids.

Neither is progress; this package stops at the exact missing source arithmetic
object above.

## Exact minimum

```text
nonreflKappaLower :
  KappaOrbitUnitsActionPairDatum G upper lower
```
with `kappaLower` not in the `refl`/conjugated-`refl` class, constructed from
actual source units action and Kummer data.  Once supplied,
`KappaOrbitUnitsActionPairDatum.layerKummer` and
`SourceEvaluationUnitPortion.ofKummerLayer` already give the actual non-refl
layer/unit portion, without a new wrapper.

Status: exact stop; no Lean file, no compile claim.
