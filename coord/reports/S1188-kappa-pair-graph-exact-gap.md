# S1188: graph KappaOrbitUnitsActionPairDatum — exact first gap

Date: 2026-10-30. No wrapper. S1184 was fixed and compiles (actual
single-factor non-refl Kummer isomorphism). S1187 is absent.

## 1. Actual fixed S1184

`tmp/sheaf/xif/paper/S1184NonReflKummerActual.lean` now compiles EXIT=0.

For an actual `φ : FPrimeStripEquiv upper lower`, `v : V`, it constructs:

```lean
stripEquivKummerIso :
  TimesMuKummer.Isomorphism (upper.unitsAction v)
    ((lower.unitsAction v).comp (φ.isoPi v))
```

with `equiv := quotientUnitsEquiv (Units.mapEquiv (φ.isoMon v))`, actual
equivariance and actual invariant-image law.  It is generally non-refl.

## 2. What the graph construction needs

Target:

```lean
G := (v : V) → upper.toDPrimeStrip.Pi v
factorUpper v := eval v : G →* upper.Pi v
factorLower v := (φ.isoPi v).comp (eval v)
sourceUnits v := (upper.Mon v)ˣ
sourceAction v := (upper.unitsAction v).comp (eval v)
kappaUpper v := TimesMuKummer.Isomorphism.refl (sourceAction v)
kappaLower v := lifted S1184 stripEquivKummerIso along eval v
```

Then `kappaUpper` is refl and `layerKummer` gives the non-refl layer.

## 3. First exact failure

The obstacle is the invariant-image law under the non-surjective? evaluation
map.  More precisely, lifting a `TimesMuKummer.Isomorphism` from the factor
group `upper.Pi v` to the product group `G` along

```text
eval v : (v : V) → upper.Pi v →* upper.Pi v
```

requires an open-subgroup comparison:

```text
fixedSubgroup (upper.unitsAction v) (H.map (eval v))
  = fixedSubgroup (upper.unitsAction v.comp (eval v)) H
```

for every open subgroup `H ≤ G`, together with openness of the image/map.
None of the existing source files states this product/evaluation open-subgroup
lemma.  `S1184.stripEquivKummerIso.invariantImage` is only for open subgroups
of the single factor `upper.Pi v`, not of `G`.

Therefore `kappaLower` cannot be filled by directly transporting the S1184
isomorphism; the first exact sublemma is:

```lean
def EvaluationOpenSubgroupLemma : Prop := ...
  ∀ (H : OpenSubgroup ((v : V) → upper.Pi v)),
    fixedSubgroup (upper.unitsAction v) (H.map (eval v)) =
      fixedSubgroup ((upper.unitsAction v).comp (eval v)) H
```

plus the corresponding target-side equality for
`(lower.unitsAction v).comp (φ.isoPi v)` and the same product map.

## 4. Alternative exact gap

One may instead set `G := upper.Pi v` (single factor), where S1184 applies
without a product lift: `factorUpper := id`, `factorLower := φ.isoPi`,
`sourceAction := upper.unitsAction v`.  This gives an actual PairDatum on the
single factor, but not the requested `G = ∏ upper.Pi`; the product version
still needs the evaluation open-subgroup lemma.

## 5. Consumer

`KappaOrbitUnitsActionPairDatum.layerKummer` (SourceKappaOrbitUnitsActionSupply
line 375) and, downstream, `layerOfPair` / `kummerOfPair` in
`KummerEvaluationArrowsActual2`.  Supplying the product-lifted `kappaLower`
would let those consumers produce the non-refl `SourceTimesMuKummerLayer`.

## Verdict

- actual: fixed S1184 single-factor non-refl Kummer isomorphism (EXIT=0).
- absent: S1187.
- exact first gap: product evaluation open-subgroup fixed-subgroup equality
  needed to lift S1184 to `G = ∏ upper.Pi`.
- no wrapper and no fake PairDatum; EXIT=0 report.
