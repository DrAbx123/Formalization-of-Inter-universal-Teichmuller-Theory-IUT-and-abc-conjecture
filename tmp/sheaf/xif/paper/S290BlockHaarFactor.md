# S290: block thetaScalingHaarFactor at uniformizer/prime

Date: 2026-10-29. Object-first; no inequality.

## Uniformizer

thetaScalingHaarFactor_eq_rootHaarFactor (S288) identifies the block factor
with rootHaarFactor.  rootHaarFactor_uniformizer_eq_norm_pow (S284) gives

  rootHaarFactor(rootUniformizerField)
    = ofReal(||rootUniformizerField|| ^ d),

where d = finrank over Qp of the root extension.  Hence the block factor at the
uniformizer equals ofReal(||pi||^d).

## Prime

Similarly, the block factor at rootPrimeFieldUnit equals
ofReal(||algebraMap p||^d), using rootHaarFactor_prime_eq_norm_pow.

No general-lambda formula beyond the uniformizer/prime cases is asserted here.

No fake factor/sorry/axiom/True/PUnit; no inequality.
