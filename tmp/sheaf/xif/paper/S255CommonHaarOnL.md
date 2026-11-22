# S255: blockHaar pushforward to L and actual Haar scalar

Date: 2026-10-29. Object-first; no inequality.

## Construction

blockLinearIsometryEquiv is the actual continuous linear isometry
rootTensorBlock ≃ L (RootTensorThetaHullActual).  Define

  commonHaarOnL b = (blockHaar T b).map (blockLinearIsometryEquiv T b).

commonHaarOnLIsAddHaar proves it is an additive Haar measure on L via
ContinuousLinearEquiv.isAddHaarMeasure_map.

commonHaarScalarFactor b = Measure.addHaarScalarFactor
  (commonHaarOnL b) (rootNormedHaar T b).

commonHaarOnL_eq_smul_open proves Haar uniqueness: on every open set,
commonHaarOnL b s = scalar • rootNormedHaar b s.

CommonHaarScalarObject packages the actual commonHaarOnL, rootNormedHaar,
and actual scalar; commonHaarScalarObject is the actual instance.

No measurable-space gap, no fake Haar/scalar/sorry/axiom/True/PUnit.
