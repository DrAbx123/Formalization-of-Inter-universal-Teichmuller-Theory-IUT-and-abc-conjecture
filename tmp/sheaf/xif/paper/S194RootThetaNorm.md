# S194: actual root-theta norm normalization

Date: 2026-10-29. Object-first; no inequality.

## Actual normalized root norm

For each v,

  rootThetaNorm v = ||G.qUnit v||^(1/(2l)),

with actual positivity and the exact power relation

  (rootThetaNorm v)^(2l) = ||G.qUnit v||.

This is not a Prop gap: it is an actual real-valued normalization computed from
the actual q unit norm in the completion, corresponding to theta = q^(1/(2l)).

## Object

RootThetaNormNormalizationObject packages:

* the actual root unit family paperRootThetaUnit j v;
* the actual q unit values in the completion;
* the actual rootNorm = rootThetaNorm;
* rootNorm_pos and rootNorm_pow_twoL (actual proofs);
* the completion additive Haar at each place.

rootThetaNormNormalizationObject is the actual instance.

No fake norm/sorry/axiom/True/PUnit; no inequality.
