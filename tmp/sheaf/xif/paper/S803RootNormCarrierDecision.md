# S803: norm carrier decision

Date: 2026-10-30. New carrier replaces old tensor-norm goals.

## Actual (RootNormQVBlock)

* rootNormCarrier_norm_eq_actual:
    ||x|| = ||rootNormLinearEquiv x|| by rfl.
* S803RootNormPreservingActual holds by rfl (s803RootNormPreservingActual_holds).
* S771 rootNormBlockIsometryEquiv : RootNormQVBlock ~ rootBase.
* S784 containments qPilotNormRegion subset rootNormHull and theta scaled
  region subset theta hull transfer accordingly.

## Old carrier: exact/impossible

* S717 TensorFractionalLatticeNormLemma: old tensor coordinate norm target;
  not asserted.
* S720 QVFamBlockNormPreserving: old target; no inhabitant
  (S803OldNormPreservingGoal).
* S723 S723ExactGoal: same old norm-preservation target; replaced.
* S720 QVFamBlockMapsFractionalLattice (lattice into padic ball): remains the
  exact maps-lattice goal S803MapsLatticeGoal (S724 attempted, not closed).
* S717 old TensorFractionalLatticeNormLemma remains S803OldTensorNormLemmaStatus
  with no proof.

Reason: the old qVFamTensorBlock norm is the FinitePadicTensor coordinate sup
norm; rootBase is the spectral norm. They are not identified; Qp(sqrt p) is
the standard counterexample shape.

## New exact target

S803RootNormLatticeBoundRequired R:
  for x in RootNormTensorFractionalLattice,
    ||x||_RootNormQVBlock <= R.

This is the root-norm replacement of S717/S720/S723 norm lemmas. No radius is
asserted; only carrier-level norm preservation is actual.

No fake norm equality; old norm instance unchanged.
