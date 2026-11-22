# S899: c_norm = order under e_v = 1

Date: 2026-10-30. Conditional on the S826 norm-compatibility and e_v=1.

## S826 input

For e : Real with 0 < e and QVFamNormalizedNormCompatibility T b e
(||q|| = p^(-(order/e))), S826 gives
  qVFamNormalizedCoefficient T b = order / e
and
  c_norm = order <-> e = 1.

Here e is instantiated with the actual
paperRamificationExponent (S819), which is positive by S840.

## Actual conditional theorem

cNorm_eq_order_of_ramification_one
  (hcompat : QVFamNormalizedNormCompatibility T b (paperRamificationExponent T b : Real))
  (he : paperRamificationExponent T b = 1) :
  qVFamNormalizedCoefficient T b = order.

## Hq

hqWeightedCNormOrder_of_ramification_one
  (hcompat : S899NormCompatibility T)   -- all places
  (he : S899RamificationOne T)          -- all e_v = 1
  : HqWeightedCNormOrder T,
via S894 hqWeightedCNormOrder_of_cNorm_eq_order.

Pointwise weighted-term form:
hq_term_eq_zero_of_ramification_one.

## Exact conditional hypotheses

S899NormCompatibility T :=
  forall b, QVFamNormalizedNormCompatibility T b (paperRamificationExponent T b : Real).

S899RamificationOne T :=
  forall b, paperRamificationExponent T b = 1.

S899HqActualRequired T := HqWeightedCNormOrder T remains the actual target;
no inhabitant for either hypothesis is asserted.
