# S927: final weighted inequality assembly

Date: 2026-10-30. Inequality only.

## Per-b V

perBVRGlobal b := normalized log-volume of s914R b = qPilotPaperRegion b.
perBVSGlobal b := normalized log-volume of s914S b = paperRootThetaHullNonzero b.

## Final target

paperWeightedInequality :=
  weightedPaperV (fun b => V(R_b)) <= weightedPaperV (fun b => V(S_b)),
where weightedPaperV uses the actual nativeBadLocalWeight and S919's
weightedPaperV_mono (nonnegative weights).

## Actual conditional theorem

paperWeightedInequality_of_interior_finite:
  (forall b, S921RInteriorNonempty b) ->
  (forall b, mu_b (S_b) < top) ->
  paperWeightedInequality.

Proof:
* each per-b inequality V(R_b) <= V(S_b) is
  S924.s924V_R_le_V_S_of_interior_finite (S914 R subset S + S921 positivity);
* S919.weightedPaperV_mono lifts to the finite weighted sum.

paperWeightedInequality_of_package uses the bundled
S927InteriorFinitenessHypotheses.

## Exact hypothesis list

* interior nonempty of every R_b;
* finiteness mu_b(S_b) < top.

No equality, no scaling data, no hull-log formula, no c_norm=order.
