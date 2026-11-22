# PaperWeightedThetaSignedActual formula check

Date: 2026-10-29. Analysis only.

## File checked

tmp/sheaf/xif/paper/PaperWeightedThetaSignedActual.lean (volumedet).

## Exact formula

For the full actual bad family and the actual unit group

  ProcessionLabel l = (ZMod l.value)^x,

the file defines, for b : Bad (nativePlaceSelection T) and j : ProcessionLabel l,

  weightedThetaLocalLog T b j
    = Real.log (thetaValueFromQ T b
        (SignedLabel.representative l.value (j : ZMod l.value))),

  weightedThetaLocalAverage T b
    = processionAverage l (weightedThetaLocalLog T b)
    = (1/(l.value - 1)) *
        sum_{j in F_l^x} weightedThetaLocalLog T b j,

  weightedThetaSignedScalar T
    = sum_b nativeBadLocalWeight T b * weightedThetaLocalAverage T b.

The comparison target is

  weightedThetaSignedScalar T
    >= nativeGlobalQPilotNormalizedSignedLogVolume T
  = -nativeGlobalQPilotNormalizedLogMagnitude T.

## Checks against the intended paper scalar

1. F_l^x labels are units, not SignedLabel including 0.
   - ProcessionLabel l is defined in ProcessionNormalizationWeightsActual as
     (ZMod l.value)^x.
   - The cardinality used by processionAverage_formula is l.value - 1.
   - SignedLabel.representative converts the unit to its centered
     representative before evaluating thetaValueFromQ; this is the correct
     j in F_l^x index.
   - No zero label is averaged.

2. Theta value is q_v^(j^2), not a raw log.
   - thetaValueFromQ T b j is
     (baseQReal T b) ^ (gaussExponent j.1).toNat.
   - baseQReal T b = ||(baseQ T b).q|| comes from the same native base q
     family used by the q-pilot side.
   - Real.log is applied only to this actual positive theta value.

3. Place weights agree with the q-side.
   - Both sides use nativeBadLocalWeight T b, i.e. the actual Remark 3.1.1(ii)
     weight from VbadPlaceIndexingActual / ProcessionNormalizationWeightsActual.
   - The F_l^x average is applied only to the theta log values inside each bad
     place; the q-pilot label family is constant under the F_l^x action, so its
     F_l^x average is the same q magnitude.  This is consistent, not a second
     place weight.

4. Sign direction.
   - Individual theta logs are negative for contracting theta values.
   - weightedThetaSignedScalar is negative and is the signed form of
     -|log Theta|.
   - nativeGlobalQPilotNormalizedSignedLogVolume is negative -|log q|.
   - The target
       weightedThetaSignedScalar >= nativeGlobalQPilotNormalizedSignedLogVolume
     is exactly Corollary 3.12's
       -|log Theta| >= -|log q|.
   - It is a Prop/target, not an asserted inequality.

5. No over-strong compatibility.
   - The file does not import or construct IQHullLogVolumeInterface, a carrier
     equivalence, or a unit-region normalization equality.
   - It uses only the scalar theta values, the actual F_l^x labels, the actual
     place weights, and the two real scalars needed by the final comparison.

## Dependency/API note

A targeted compile attempt showed the formula file is blocked by upstream
errors in GlobalQPilotProcessionLogVolumeActual (canonicalProcession application
and qPilotProcessionLogVolume binder order), not by the formula in
PaperWeightedThetaSignedActual itself.  Those are API-level dependency issues;
the formula/weight choices above are the intended minimal scalar and do not
require a full interface.

## Verdict

The formula in PaperWeightedThetaSignedActual is the correct minimal scalar
shape:

  (1/|F_l^x|) sum_{j in F_l^x} log(q_v^(j^2)), weight by
  [K_v:(F_mod)_v]^{-1}, summed over V_bad.

It uses units, consistent place weights, the actual native q family, and no
over-strong IQ/carrier compatibility.  The remaining work is closing the
upstream API errors, not changing the scalar formula.
