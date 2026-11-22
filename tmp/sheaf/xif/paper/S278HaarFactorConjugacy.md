# S278: partial conjugacy for block/root Haar factors

Date: 2026-10-29. Object-first; no inequality.

## Proved

image_blockScaling_unitBall: the continuous linear isometry conjugates block
scaling to L multiplication at the set level:

  e '' (blockScaling lam '' blockUnitBall)
    = (fun x => lam * x) '' rootExtensionUnitBall.

## Remaining exact requirement

The final scalar equality thetaScalingHaarFactor = rootHaarFactor still
requires the measure-transport calculation on the scaled set with
blockHaar_map_eq_inv_smul_rootExtensionHaar and the Haar factor ratio.  It is
recorded as BlockRootHaarFactorEqualityGap/Required, with no inhabitant.

No fake factor/sorry/axiom/True/PUnit; no inequality.
