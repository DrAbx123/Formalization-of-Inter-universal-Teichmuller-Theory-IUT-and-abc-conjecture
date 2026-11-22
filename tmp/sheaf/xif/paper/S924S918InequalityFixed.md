# S924: corrected S918 inequality (no coefficient equality)

Date: 2026-10-30. Inequality only.

## Inputs

* S914.s914R_subset_S: R = qPilotPaperRegion subset S = paperRootThetaHullNonzero.
* S921.s921R_measure_pos_of_interior:
    S921RInteriorNonempty -> 0 < mu R.
* S924SHullFinite: mu S < top (exact remaining finiteness input).

No c_norm = order, no scaling data, no hull log equality, no numeric formula.

## Results

s924R_measure_pos_of_interior: positivity of R from S921.

s924V_R_le_V_S_of_interior_finite:
  S921RInteriorNonempty ->
  mu S < top ->
  V(R) <= V(S),
where V is arithmeticTupleNormalizedLogVolume on s914R/s914S, via S914's
arithmeticTupleNormalizedLogVolume_mono.

s924InequalityPackage: conjunction of R subset S, 0 < mu R, mu S < top,
and V(R) <= V(S).

S924FiniteSHullRequired records the exact finiteness input; no equality route.
