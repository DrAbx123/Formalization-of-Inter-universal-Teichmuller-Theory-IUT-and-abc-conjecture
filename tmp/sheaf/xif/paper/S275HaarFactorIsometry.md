# S275: block/root Haar factor comparison obstruction

Date: 2026-10-29. Object-first; no inequality.

## Status

The actual factors are available:

* thetaScalingHaarFactor (block scaling Haar scalar);
* rootHaarFactor (root extension distribution character).

The actual isometry blockLinearIsometryEquiv and its measure transport
(RootTensorHaarIsometryActual.blockHaar_map_eq_inv_smul_rootExtensionHaar) are
also available.

However the factor equality requires transporting the scaling map through the
isometry and commuting the Haar scalar factors; a direct proof is not completed
in this file.  No equality is asserted without it.

BlockRootHaarFactorComparison records the actual blockFactor, rootFactor, and
the exact scalar_relation Prop; BlockRootHaarFactorComparisonRequired is its
nonemptiness, no inhabitant.

No fake factor/sorry/axiom/True/PUnit; no inequality.
