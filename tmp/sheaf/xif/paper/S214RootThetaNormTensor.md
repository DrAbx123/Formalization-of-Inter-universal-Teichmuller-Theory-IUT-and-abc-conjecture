# S214: rootThetaNorm and the L tensor theta norm/hull transport

Date: 2026-10-29. Object-first; no inequality.

## Actual transport

For the one-factor tensor block there is the actual linear equivalence

  tensorBlockLinearEquiv : rootTensorBlock T b ≃ₗ[Qp] rootNormedExtension T b.

The tensor theta image maps exactly to the L value:

  tensorBlockLinearEquiv (rootTensorThetaImage j) = rootNormedThetaValueInL j.

The transported tensor theta norm (measured by the actual L norm) is

  transportedTensorThetaNorm j = ||tensorBlockLinearEquiv (rootTensorThetaImage j)||
    = ||rootNormedThetaValueInL j||
    = ||rootNormedElement||^(gaussExponent j).

## Hull

LThetaClosureHull = closure (range rootNormedThetaValueInL).

tensorThetaHullPreimage = tensorBlockLinearEquiv^{-1}(LThetaClosureHull).

The compatibility object RootThetaNormTensorHullCompatibility bundles the S201
root norm object, the tensor theta image, the transported theta norms, the
tensor hull preimage, the L closure hull, and the exact hull compatibility
  tensorBlockLinearEquiv '' tensorHull = LThetaHull.

No fake norm/sorry/axiom/True/PUnit; no inequality.
