# S2720 Cor312 -> ABC bridge: assembly status

Date: 2026-11-07. Source base: `tmp/sheaf/xif/paper/S2720BridgeActualObjActual.lean`
(source SHA `79FB007C4082D671EDE83825343BAC46E73E5679600C9EA7E4863751C50EEF80`).

**Status: base file has NO olean; the bridge is NOT actual.** The two defs
`bridgeInterfaceS2586` and `bridgeInterfaceS2586Full` are conditional on the six
inputs below. This document records exactly which inputs are available; it does
not fake the final bridge.

## 1. Actual infrastructure (already in tree)

| component | artifact | status |
|---|---|---|
| carrier `qVFamTensorBlock T b` | S2720 source imports | actual per-block carrier object; S2720 itself no olean |
| hullData `S2586IQHullLogVolumeInterface T b` | S2586IQHullLogVolumeInstantiationActual (olean 82472 B, SHA 73012D74...) | ACTUAL |
| point `S2588PointMap T b a n c` | S2588RationalPointMapActual (olean 63208 B, SHA EB51CA56...) | ACTUAL |
| eps comparison `S2594_epsilonComparison` | S2594HpointWiringActual (olean 55424 B, SHA B88933C2...) | ACTUAL conditional def |
| hnull predicate `S2589SingletonNull` | S2589DictionaryMinimalActual (olean 28384 B, SHA D0280DA5...) | DEFINED Prop; NO inhabitant |
| theta hull/measure transport (different carrier) | S2742ThetaActualHullTransport / S2742MeasureTransportActual | ACTUAL, but for `OriginalInput` theta carrier, not this S2720 carrier |
| point-dependent region (bad-only carrier) | S2730PointScalingComparisonActual | ACTUAL, but bad-only carrier; insufficient for full ABC support |

## 2. The six explicit inputs of `bridgeInterfaceS2586Full`

| input | type (abridged) | current status | remaining work |
|---|---|---|---|
| `hnull` | `S2589SingletonNull (S2586IQHullLogVolumeInterface T b)` | predicate defined, NO inhabitant | prove singleton-null for the S2586 interface |
| `hval` | `forall eps>0, forall ABC triple, forall q in support, max 0 (-padicValRat q point) <= 1+eps` | NOT supplied | actual q/padic valuation bound; depends on actual q normalization |
| `hweightvol` | `forall ABC triple, arithmeticWeight point <= logVolume normalizedComparisonRegion` | NOT supplied; only S2743 conditional | support-complete arithmeticWeight/region-volume comparison (S2748/S2749/S2750/S2751 chain, full support) |
| `hunit` | `logVolume unitRegion <= logVolume hull + 0` | NOT supplied at this carrier | actual unit-region vs hull volume inequality |
| `hsplit` | `logVolume region <= logVolume (scaleShift '' unitRegion) + logVolume {scaleShift point}` | NOT supplied at this carrier | actual point-dependent region splitting/measure formula |
| `hptfin` | `logVolume {scaleShift point} < top` | NOT supplied at this carrier | finiteness of the point measure (and point is not measure-zero issue must be handled) |

## 3. Exact remaining list

1. Compile `S2720BridgeActualObjActual` (currently NO olean); fix source if needed.
2. Supply `hnull` inhabitant for the S2586 IQ-hull interface.
3. Supply `hval` (actual q/padic valuation bound in the paper normalization).
4. Supply `hweightvol` with FULL ABC support (bad-only carriers insufficient;
   S2743 is conditional only; S2748/S2749/S2750/S2751 chain is the current route).
5. Supply `hunit`, `hsplit`, `hptfin` for the S2720 carrier, using actual
   unit/hull/point measure facts (S2742 is on a different carrier; S2730 region
   is bad-only).
6. Only then `bridgeInterfaceS2586Full` yields `Cor312ToABCBridgeInterface`;
   do not claim the final bridge earlier.

## 4. Non-fake constraints

- No `sorry`, `axiom`, `True`, `PUnit`, or arbitrary inhabitant may replace any of
  the six inputs.
- `hval` and `hweightvol` must remain explicit hypotheses in the skeleton until
  actual objects are supplied.
- The fixed-scale and unit-line-bundle routes are known false/insufficient and
  must not be used.
