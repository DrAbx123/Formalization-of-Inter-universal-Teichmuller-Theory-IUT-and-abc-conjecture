# S201: rootThetaNorm vs the actual L norm

Date: 2026-10-29. Object-first; no inequality.

## Actual L norm facts

rootNormedElementNorm = ||rootNormedElement||.

rootNormedElementNorm_pow_twoL:
  (||rootNormedElement||)^(2l) = ||sourceRootQUnit||.

rootNormedThetaValueInL_norm:
  ||rootNormedThetaValueInL j|| = ||rootNormedElement|| ^ (gaussExponent j),
using the actual zpow norm in L.

## Comparison with S194 rootThetaNorm

rootThetaNorm_eq_rootNormedElementNorm: for a completion geometry G whose qUnit
norm at v equals ||sourceRootQUnit||,

  rootThetaNorm G v = rootNormedElementNorm.

This uses the actual 2l-th norm powers and positivity, via pow_left_inj₀.

## Object

RootThetaNormLObject packages the actual L root norm, its 2l-th power identity,
and the actual root theta value norms rootNormedThetaValueInL j.

rootThetaNormLObject is the actual instance.

No fake norm/sorry/axiom/True/PUnit; no inequality.
