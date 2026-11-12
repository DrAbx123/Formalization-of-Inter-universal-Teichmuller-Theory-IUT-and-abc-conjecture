# S2802 — Height comparison inventory (route III)

Date: 2026-11-07. Scope: audit of actual height-comparison fragments in the
repository / IUT IV-facing formalization. This is an inventory, not a new
assembly claim. **The point-height dictionary is NOT the height-volume
inequality** (see §6).

## 1. ThetaPilotPoint carrier / theta hull

| object | artifact | status |
|---|---|---|
| `ThetaPilotPoint`, possible theta-pilot image/hull, signed hull log-volume | `S2725ThetaImageHullActual` (olean 35432 B, SHA CD68F62F...) | ACTUAL: image/hull interface and point-mem-hull |
| global theta image set/hull/log-volume on `GlobalThetaCarrier` | `S2725GlobalThetaHullActual` (olean 129096 B) | ACTUAL: globalThetaImageSet/Hull/LogVolume, compactness/subset lemmas |
| theta hull log-volume / image-subset-hull / least candidate hull on `OriginalInput` | `S2742ThetaActualHullTransport` (olean 23928 B, SHA F7A54960...) | ACTUAL, but on the `OriginalInput` theta carrier, not on the Cor312 line-bundle carrier |
| image/hull measure transport | `S2742MeasureTransportActual` (olean 133088 B, SHA 176A66B0...) | ACTUAL, same `OriginalInput` carrier |

**Reusable:** the theta carrier and hull/volume objects are actual. **Missing for
route III:** a transport from `OriginalInput.ThetaPilotPoint` to the Cor312
line-bundle/pointed carrier (the carriers are different).

## 2. Log-shell / log-volume

| object | artifact | status |
|---|---|---|
| fractional-ideal fundamental domain + Haar volume | `S2756FractionalIdealHaarActual` (olean 56672 B, SHA 7137367E...) | ACTUAL: `S2756IdealHaarVolume_eq` (ideal norm × integer fundamental-domain volume) |
| mixed-space IQ-hull interface | `S2758MixedSpaceIQHullActual` (olean 93208 B) | ACTUAL |
| fundamental-domain scaling / Haar scaling | `S2758FundamentalDomainScalingActual` (olean 34416 B) | ACTUAL |
| paper factor `r = min 1 (absNorm J)^-1`, scaled unit region | `S2760MixedSpacePaperFactorActual` (olean 171816 B) | ACTUAL: nontrivial paper-factor IQ-hull interface |
| S2586 IQ-hull interface on qVFam block | `S2586IQHullLogVolumeInstantiationActual` (olean 82472 B) | ACTUAL interface; **hweightvol FAILS** on this carrier |
| S2727 global bad-place QVFam interface | `S2727GlobalQVFamHullActual` (olean 117128 B, SHA 330EB9CF...) | ACTUAL, but bad-only; insufficient for arithmeticWeight |

**Reusable:** actual Haar/fundamental-domain and paper-factor log-volume objects.
**Missing:** a log-volume carrier whose index contains the full ABC prime support
(bad-only carriers are insufficient; S2732 audit criterion).

## 3. Multiradial / point-dependent comparison regions

| object | artifact | status |
|---|---|---|
| S2781 pointed line-bundle region | `S2781PointedLineBundleRegionActual` (olean 125872 B, SHA A327D95A...) | ACTUAL: carrier, point, logVolume, region equality, weight≤region |
| S2766 exact epsilon-comparison gap | `S2766EpsilonComparisonGapActual` (olean 47136 B, SHA C443CB22...) | ACTUAL gap **statement** (fields are hypotheses) |
| S2767 height-gap epsilon | `S2767HeightGapEpsilonActual` (olean 130368 B) | ACTUAL reductions; no unconditional gap |
| S2730 point-dependent line-bundle/ABC region | `S2730PointScalingComparisonActual` (olean 92104 B) | ACTUAL construction; bad-only carrier |

**Reusable:** S2781 is the actual point-dependent pointed region; its log-volume
is the supremum of pointed covolume logs.

## 4. H1 / H2

### H1 (height vs arithmetic weight)

`ABCHeightArithmeticWeightComparison.lean` (olean 68688 B) is ACTUAL:

- `abcRationalPoint_logHeight₁_le_mul_arithmeticWeight_of_uniform_valuation_bound`
- `abcRationalPoint_logHeight₁_le_oneAdd_mul_arithmeticWeight_of_valuation_bound`

Both are conditional on the uniform valuation bound `hval`. **H1's `hval` is
refuted** by `no_oneAdd_valuation_bound` (family `(1, 2^k−1, 2^k)`), so the H1
premise is unsatisfiable and cannot yield an unconditional height comparison.

### H2 (region volume vs weight / point bound)

`Cor312ComparisonGapReduction.lean` (olean 308272 B) is ACTUAL:

- `cor312Gap2_regionVolume_le_normalizedWeight_of_split_pointBound_unitRegionBound`;
- `cor312Gap2_hsplit_of_mem_unitRegion`, `cor312Gap2_hptfin_of_mem_unitRegion`;
- `cor312Gap1_not_forall_arithmeticWeight_le_normalizedComparisonRegionVolume`
  (the weight≤region direction fails in the real-line calibration).

H2 is a reduction to named point/unit-region inputs; no unconditional H2.

## 5. Cor312 pointwise residual supply

`Cor312ComparisonGapSupplyLayer.lean` (olean 132896 B) is ACTUAL and contains the
pointwise residual supply:

- `cor312GapSupply_sourceSetVolume_singleton/union_le`;
- `cor312GapSupply_sourceInterface_hsplit/hptfin/hunit_of_degreeBound_le_hullVolume`;
- `cor312GapSupply_sourceInterface_weightvol_of_degreeDictionary`;
- `cor312GapSupply_sourceGap1_of_valuationBound_degreeDictionary`;
- `cor312GapSupply_sourceGap1_of_additiveBound_degreeDictionary`.

All are conditional on the degree dictionary / valuation or additive bound. The
corresponding interface assembly is
`Cor312ToABCBridgeInterface.lean` (olean 470304 B), which keeps the two gap fields
as explicit hypotheses.

## 6. pointHeightDictionary is NOT height ≤ volume

`S2587PointHeightDictionary` (S2587Cor312PointMapSkeletonActual, olean 167216 B)
is defined in the **opposite** direction:

```lean
(W.logVolume {W.scaleShift (p a b c)}).toReal ≤ Height.logHeight₁ (abcRationalPoint a c)
```

i.e. **volume(point) ≤ height**, not `height ≤ (1+eps)·volume(region)`.
`S2589SingletonNull` is only a predicate (`Prop`) with no inhabitant.

The opposite-direction dictionary
`S2776HeightDictionary : height ≤ C · regionVolume` is source-level
(`S2776BridgeHeightReduction`, olean 30016 B), but
`S2780HeightDictionaryNoGoActual` (olean 29224 B) proves it is **FALSE for every
`J, eps, C`** in the S2776/S2760 fixed-hull calibration: the comparison-region
volume is the fixed hull volume (S2767) while heights are unbounded.

**Consequence:** no `pointHeightDictionary` (volume≤height) may be used as a
height≤volume comparison. The direction matters and is documented here to prevent
that substitution.

## 7. Precise target statement for the height comparison

For the S2781 pointed region with `eps ≥ 0`, the target is

```lean
∀ a b c, IsABCTriple a b c →
  Height.logHeight₁ (abcRationalPoint a c) ≤
    (1 + eps) *
      ((S2781PointedIQHull l 1).logVolume
        (S2781ComparisonRegion l eps a b c)).toReal
```

Equivalently, after the region-log-volume identity, the missing object is

```lean
∀ a b c, IsABCTriple a b c →
  Height.logHeight₁ (abcRationalPoint a c) ≤
    (1 + eps) * max 0 (S2781CovolumeLog l (S2781LogShellPoint l a b c))
```

This is a height/region-volume dictionary; the additive version is
`ABCHeightWeightAdditiveBoundV2`, which is ABC-equivalent and cannot be assumed.

## 8. Inventory summary

**Actual reusable:** theta image/hull and measure transport (S2725/S2742);
fundamental-domain Haar and paper factor (S2756/S2758/S2760); S2781 pointed region;
H1 reductions but only under the refuted `hval`; H2 and Cor312 pointwise supply
reductions (conditional); S2780 no-go.

**Missing / blockers:**
1. carrier transport from the theta `OriginalInput` carrier to the line-bundle
   pointed carrier;
2. a support-complete log-volume carrier for arithmeticWeight;
3. the actual height/region-volume dictionary on the pointed region;
4. a non-refuted replacement for H1's `hval` (the additive replacement is ABC-hard).

**No assembly claim:** route III is not closed by this inventory.