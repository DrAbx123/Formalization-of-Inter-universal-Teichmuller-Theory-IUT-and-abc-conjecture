# S2791 height gap on the S2781 pointed region — status

Date: 2026-11-07. Owner: transport. Phase A2 (PLAN_ABC).

## What is actual

- `S2781PointedLineBundleRegionActual` (olean 125872 B, SHA A327D95A...) is ACTUAL.
  It provides a genuinely point-dependent region
  `S2781ComparisonRegion eps a b c = {1} ∪ {S2781LogShellPoint a b c}`
  on the line-bundle carrier, with `logVolume` = supremum of the pointed covolume logs.
- `S2781_weight_le_regionVolume_of_ne` is actual: for nonzero qPilot line bundle,
  `arithmeticWeight ≤ logVolume (S2781ComparisonRegion ...)`.

## Attempted proof of `S2781Gap.height_le_region`

Planned reduction:
1. prove `logVolume (S2781ComparisonRegion eps a b c)` = `ofReal (max 0 covolume(point))`;
2. convert the actual weight bound to a `toReal` inequality;
3. apply the actual H1 reduction
   `abcRationalPoint_logHeight₁_le_oneAdd_mul_arithmeticWeight_of_valuation_bound`
   with the local valuation bound `hval`;
4. multiply by `1 + eps ≥ 0`.

Step 1's upper bound compiles; the exact equality proof is blocked by a Lean
elaboration error around the union/singleton set notation:
`failed to synthesize Singleton (S2781Carrier l) Type` / `Union Type` (first error
when annotating `({1} : Set ...) ∪ {point}` inside `le_iSup`). This is a
formalization issue, not a mathematical obstruction.

Step 3 is the real mathematical obstruction: the required `hval` is REFUTED.
`Cor312ComparisonGapReduction.lean` records `no_oneAdd_valuation_bound` (family
`(1, 2^k − 1, 2^k)`, probe `H1UniformValuationBoundCounterexampleProbe.lean`), so
the H1 comparison premise is unsatisfiable. Therefore this route cannot yield an
unconditional height gap.

## Exact missing object

The height gap on the pointed region is exactly the dictionary

```lean
∀ a b c, IsABCTriple a b c →
  Height.logHeight₁ (abcRationalPoint a c) ≤
    (1 + eps) * (max 0 (S2781CovolumeLog l (S2781LogShellPoint l a b c)))
```

(after the region log-volume identity). No smaller missing object is available
from the H1 reduction, because its valuation premise is false. The additive
version of this input is `ABCHeightWeightAdditiveBoundV2`, which is equivalent to
the ABC conjecture, so it cannot be assumed; this is the exact obstruction.

## Status

- `S2791HeightGapActual`: NOT actual (no olean).
- Region construction: ACTUAL via S2781.
- Height gap: not proved; exact missing object is the height/region-volume
  dictionary above; the H1 `hval` route is refuted.
- No fake/sorry/axiom used.
