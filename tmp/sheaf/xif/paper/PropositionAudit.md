# Proposition audit: PaperXiFClosedActual versus the target xi-f statement

Date: 2026-10-29.  Status: audit; no completion claim.

## 1. The target proposition

`PaperXiFSpec.paperXiF` is

  paperXiF q thetaLog := paperSignedLog q <= thetaLog,
  paperSignedLog q = -|Real.log q|.

The existing target gate (`PaperAssemblyActualFinal` and the `PaperXiFInclusion`
surface) states the paper scalar theorem at `paperQParameter C3` with
`P.signedHullLogVolume`.

## 2. What PaperXiFClosedActual proves

`PaperXiFClosedActual` proves

  paperXiF (actualPaperQParameter T) (globalThetaHullLog T),

where

  actualPaperQParameter T = exp(globalQPilotLog T),
  globalQPilotLog T = sum_b weight_b * localQPilotLog_b,
  globalThetaHullLog T = sum_b weight_b * localThetaHullLog_b.

The current `localThetaHullLog_b` is defined as `-(c_b log p_b)`, the same
expression as `localQPilotLog_b`; it is not yet the normalized log-volume of an
actually constructed theta hull.

## 3. It is a different proposition unless a bridge is proved

The following are missing bridges:

1. `actualPaperQParameter T` versus the paper q-pilot parameter (and versus
   `paperQParameter C3` in the target surface).
2. `globalThetaHullLog T` versus `P.signedHullLogVolume` / the actual
   normalized log-volume of the paper Theta hull.
3. The relation between the qVFamily q scalar and the 2l-th root theta values.
   IUT I, Example 3.2(iv) says q_v is a 2l-th root; the theta value is
   q_v^(j^2).  The current coefficient c_b uses qVFamily order directly,
   without the 2l-root normalization, so its local scalar may differ by a
   factor 2l from the theta-hull scalar.

Therefore `PaperXiFClosedActual` is not yet the target paper-level xi-f
proposition; it is a separate scalar statement over the qVFamily model.

## 4. Consequences

- Do not count `PaperXiFClosedActual` as target completion.
- Do not connect it to `PaperAssemblyActualFinal` until the bridges above are
  actual theorems.
- The definitional equality `localThetaHullLog := localQPilotLog` must be
  replaced by an actual `arithmeticTupleNormalizedLogVolume` identity from
  `ArithmeticTuplePureFractionalScalingData`.

No sorry, axiom, True, PUnit, or toy object is used in this audit.
