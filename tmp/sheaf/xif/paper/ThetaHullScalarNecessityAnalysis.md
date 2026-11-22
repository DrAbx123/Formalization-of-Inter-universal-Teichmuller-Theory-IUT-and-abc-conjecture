# Theta hull scalar: necessity analysis and minimal actual construction

Decision: **do not build a full value-level transport from GlobalIQAmbient to
C3LogShellTensorBlock.** For the xi-f scalar used by Corollary 3.12, the needed
object is a hull log-volume and a q-pilot log-volume on actual carriers, not a
comparison of the full tensor packet with the C3 selected tuple block.

## 1. What xi-f actually needs

Corollary 3.12 uses the scalar

  -|log(Theta)| = procession-normalized mono-analytic log-volume of the
  holomorphic hull of the union of possible Theta-pilot images,

and compares it with the q-pilot scalar

  -|log(q)| = procession-normalized mono-analytic log-volume of the q-pilot image.

The xi-f consumer needs:

1. an actual Theta-pilot image/hull and its normalized log-volume;
2. an actual q-pilot log-volume;
3. the comparison proposition between the two scalars.

It does not need:

- a map GlobalIQAmbient j -> C3LogShellTensorBlock;
- an identification of the extra Fin(j+1) tensor factors with the C3 selected
  tuple;
- a full log-shell/tensor-packet carrier equivalence;
- a line-bundle/theta-function identification.

## 2. Why the full transport is not canonical

The two carriers are different objects:

- GlobalIQAmbient j = ArithmeticPacketTensor (literalIQPlaces j) is a tensor
  over Fin(j+1) x C3.tensorIndex, with one CompletionPacket factor for each
  procession level and C3 tensor index.
- C3LogShellTensorBlock C3 is the tensor over C3.tensorIndex of the
  selected-tuple completion factors.

For j = 0, the extra index is Fin 1 and the actual index equivalence
LiteralIQIndex 0 ~= C3.tensorIndex plus the actual tuple projection can collapse
the unique factor. This is the actual globalIQToC3HullLevelZero object.

For j > 0, collapsing the j+1 completion-packet factors to one selected
completion requires:

- choosing one procession level;
- selecting a normalization/unit value in all remaining factors;
- proving that this choice is compatible with the paper's Fin(j+1)-symmetry.

The paper does not supply such a canonical choice. Therefore the general
GlobalIQAmbient j -> C3LogShellTensorBlock transport is an exact object-level
gap, not something to fake.

## 3. Minimal actual construction

The minimal actual scalar data is on the actual source carrier, not on a
cross-carrier comparison.

### Carrier
- actual source value point carrier I.ThetaPilotPoint v;
- actual global Theta-pilot carrier (v : V) -> I.ThetaPilotPoint v when the
  global scalar is needed.

### Actual Theta image/hull
- I.possibleThetaPilotImageSet v R n;
- I.sourceHolomorphicHull v R n;
- actual containment
  I.possibleThetaPilotImage_subset_sourceHolomorphicHull.

### Actual positive hull log-volume
- positivePointLogVolume = -I.sourceLocalLogDegree;
- positiveSetLogVolume = sup of positive point log-volumes;
- positiveHullLogVolume = positiveSetLogVolume of the actual source hull.

These are the corrected positive objects of
SourceHullVolumeSignCorrectedActual. They do not use the old truncated
ENNReal.ofReal (sourceLocalLogDegree) construction.

Equivalently, the actual global scalar can be taken from
GlobalPositiveThetaHullLogVolumeActual.globalThetaHullPositiveLogVolume,
which is the sum of the actual positive theta log-volumes over places and is
defined directly from actual theta values and actual hull membership.

### Actual q-pilot scalar
- actual baseQLogMagnitude T b at a bad place, or the actual global q-pilot
  sum after the finite Bad type is supplied;
- no raw log(1/5) and no finite C3 packet substitution.

### Comparison
The comparison thetaHullLog <= qPilotLog remains the exact xi-f scalar
comparison proposition. It is not an object-level transport and not an
inequality asserted by the carrier construction.

## 4. What WeakThetaHullDataActual already contains

After the sign correction, WeakThetaHullDataActual.lean has:

- weakThetaImageSet = I.possibleThetaPilotImageSet;
- weakThetaHull = I.sourceHolomorphicHull;
- actual image-hull containment;
- weakThetaImageVolume = positiveSetLogVolume on the actual image set;
- weakThetaHullVolume = positiveHullLogVolume;
- weakThetaHullLog = positiveHullLogVolume.toReal;
- qPilotLog = baseQLogMagnitude T b;
- thetaHullLeQPilot = (hullLog <= qPilotLog) as a Prop.

This is already on a single actual source carrier. It does not need
GlobalIQAmbient, C3LogShellTensorBlock, or a value-level transport.

## 5. Recommendation

1. Keep WeakThetaHullDataActual as the minimal scalar data layer.
2. Do not use GlobalIQToC3HullTransportActual on the critical xi-f path.
3. Retain globalIQToC3HullLevelZero only as an actual level-0 observation;
   retain the general ExtraFactorCollapseGap only as an audit/gap record.
4. If a global scalar is needed, use
   GlobalPositiveThetaHullLogVolumeActual.globalThetaHullPositiveLogVolume
   on the actual product carrier.
5. The only remaining xi-f scalar step is the actual comparison
   thetaHullLog <= qPilotLog, not a carrier transport.

No fake carrier comparison, no fake image inclusion, and no inequality is
asserted by this minimal construction.
