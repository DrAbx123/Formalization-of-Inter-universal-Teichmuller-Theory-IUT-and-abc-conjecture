# S683: Mathlib operator-norm tools for QPilotRadiusBoundObstacle

Date: 2026-10-30. Research only; conditional lemma compiled.

## Target

S671:
  QPilotRadiusBoundObstacle T b cNorm :=
    forall x in qPilotClassicalRegion ..., ||qPilotToRootExtension x|| <= rootImageRadius.
Equivalent to per-b containment:
  perBContainment_iff_radiusBound.
S671 also proves the product coordinate is exactly a closed ball:
  rootImageCoordinate_eq_closedBall :
    rootImageCoordinate = Metric.closedBall 0 rootImageRadius.

## Mathlib theorems available

Operator norm:
* ContinuousLinearMap.opNorm_le_bound
* ContinuousLinearMap.opNorm_le_bound'
* ContinuousLinearMap.le_opNorm
* ContinuousLinearMap.le_opNorm_of_le
* SemilinearMapClass.bound_of_continuous
  (a continuous semilinear map has a positive multiplicative norm bound).

Finite-dimensional continuity:
* LinearMap.continuous_of_finiteDimensional
  (finite-dimensional Hausdorff TVS over a complete field).
* LinearEquiv.toContinuousLinearEquivOfBounds
* LinearEquiv.toContinuousLinearEquivOfContinuous (Banach)
* ContinuousLinearEquiv.ofFinrankEq
* LinearEquiv.toContinuousLinearEquiv / toLinearEquiv_toContinuousLinearEquiv
  (finite-dimensional normed spaces).

Closed balls / lattice:
* Metric.closedBall, Metric.mem_closedBall, dist_eq_norm
* closure/submodule lattice operations through Set/Submodule; there is no
  Mathlib "fractional lattice radius" theorem.  qPilotClassicalRegion is the
  actual fractional-lattice scaled region from RootHullContainmentInequality.

## Conditional lemma (compiled)

qPilotRadiusBound_of_operatorConstant:
  given C >= 0,
        hC : forall x, ||qPilotToRootExtension x|| <= C * ||x||,
        hregion : forall x in qPilotClassicalRegion, ||x|| <= R,
        hbound : C * R <= rootImageRadius,
  proves QPilotRadiusBoundObstacle.

This is the exact shape accessible from Mathlib opNorm/SemilinearMapClass.bound_of_continuous:
the operator gives C, and the remaining datum is the source-region radius bound.

## Exact remaining gaps

1. Source-region norm bound: forall x in qPilotClassicalRegion, ||x|| <= R.
   This is not a Mathlib norm theorem; it is a source fractional-lattice radius
   statement.
2. A compiled actual operator bound for qPilotToRootExtension.  S678 attempted
   LinearMap.continuous_of_finiteDimensional + SemilinearMapClass.bound_of_continuous,
   but the current qVFamTensorBlock/rootNormedExtension instances did not supply
   the required Norm/ContinuousSMul instances in the local compile; that file is
   not used here.  S683 works with the explicit constant C.

No fake norm/radius; no operator constant is asserted.
