# S288: thetaScalingHaarFactor = rootHaarFactor

Date: 2026-10-29. Object-first; no inequality.

## Computation

thetaScalingHaarFactor_spec on blockUnitBall gives

  blockHaar (Tlam '' blockUnitBall)
    = thetaScalingHaarFactor lam * blockHaar(blockUnitBall),

and blockHaar(blockUnitBall)=1, so the factor equals the block image mass.

The continuous linear isometry e maps Tlam '' blockUnitBall to
lam • rootExtensionUnitBall (S278 image equality).  The pushed block Haar is
rootNormedHaar (S264: commonHaarOnL = rootNormedHaar), hence

  blockHaar (Tlam '' blockUnitBall)
    = rootNormedHaar (lam • rootExtensionUnitBall).

The distribution-character formula distribHaarChar_eq_div on rootNormedHaar and
rootExtensionUnitBall gives

  rootHaarFactor lam
    = rootNormedHaar (lam • rootExtensionUnitBall)
      / rootNormedHaar (rootExtensionUnitBall)
    = rootNormedHaar (lam • rootExtensionUnitBall).

Therefore thetaScalingHaarFactor lam = rootHaarFactor lam.

No fake factor/sorry/axiom/True/PUnit; no inequality.
