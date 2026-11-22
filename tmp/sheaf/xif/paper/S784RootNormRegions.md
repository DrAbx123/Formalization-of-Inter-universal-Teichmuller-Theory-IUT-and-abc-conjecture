# S784: rebase regions to RootNormQVBlock

Date: 2026-10-30. Actual transfer + conditional norm bounds.

## Transfer

rootNormSet S := {x : RootNormQVBlock T b | x.toBlock in S}.

Carried regions:
* rootNormQPilotRegion = transfer qPilotClassicalRegion(cNorm);
* rootNormQPilotNormRegion = transfer qPilotNormRegion;
* rootNormHullCarrier = transfer rootNormHull;
* rootNormThetaScaledRegion c = transfer thetaTensorScaledRegion c;
* rootNormThetaHull c = transfer thetaTensorHull c.

## Actual containments

rootNormQPilotNormRegion_subset_rootNormHull:
  transfer qPilotNormRegion subset transfer rootNormHull,
  from qPilotNormRegion_subset_rootNormHull.

rootNormThetaScaled_subset_rootNormThetaHull:
  transfer thetaTensorScaledRegion(cfun j) subset transfer thetaTensorHull(cfun),
  from subset_closure and Set.mem_iUnion.

## Norm bound on the new carrier

rootNormCarrier_norm_eq x:
  ||x|| = ||qVFamBlockLinearEquiv x.toBlock||_rootBase
by rfl (the carrier norm is pulled back).

Conditional bounds:
* RootNormQVPilotBound R: for x in qPilotNormRegion,
  ||qVFamBlockLinearEquiv x|| <= R;
  rootNormQPilot_norm_le transfers it to all x in the rebased region.
* RootNormThetaScaledBound c R for thetaTensorScaledRegion;
  rootNormThetaScaled_norm_le transfers it.

## Paper-faithfulness audit

The old qVFamTensorBlock coordinate norm is unchanged. RootNormQVBlock is a
separate carrier whose norm is by construction the rootBase norm; the
isometry is S771's rootNormBlockIsometryEquiv with rfl norm_map.

Therefore:
* carrier-level isometry is actual;
* region containment transfers actual;
* the numeric radius bounds are exact conditions RootNormQVPilotBound /
  RootNormThetaScaledBound, not proved from the old coordinate norm.

No fake norm equality.
