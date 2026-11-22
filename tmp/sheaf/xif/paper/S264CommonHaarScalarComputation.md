# S264: calculation of commonHaarScalarFactor

Date: 2026-10-29. Object-first; no inequality.

## Unit-ball image

blockLinearIsometryEquiv maps blockUnitBall onto rootNormedUnitBall
(closed norm balls are preserved by the isometry).

commonHaarOnL_unitBall: the pushed block Haar assigns mass 1 to the L unit ball
(map_apply + preimage/image + blockUnitBall_measure = 1).

rootNormedUnitBall_measure: rootNormedHaar gives mass 1 to the same unit ball.

## Scalar

commonHaarScalarFactor_eq_one: using addLeftInvariant Haar uniqueness
(isAddLeftInvariant_eq_smul) and evaluating at rootNormedUnitBall, the scalar is
1.

commonHaarOnL_eq_rootNormedHaar: hence the pushed block Haar equals
rootNormedHaar exactly.

No fake Haar/scalar/sorry/axiom/True/PUnit; no inequality.
