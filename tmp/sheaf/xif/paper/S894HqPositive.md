# S894: positive HqWeightedCNormOrder

Date: 2026-10-30. Direct proof from per-b c_norm = order.

## Direct theorem

hqWeightedCNormOrder_of_cNorm_eq_order:
  (∀ b, qVFamNormalizedCoefficient T b = order(qVFamily T b))
  -> HqWeightedCNormOrder T.

Proof: unfold the finite sum, apply Finset.sum_eq_zero, and each weighted term
has (c_norm - order) = 0; ring closes.  No weight nonneg/positivity condition
is used.

Pointwise form: hq_weighted_term_eq_zero_of_cNorm_eq_order.

## S817/S825 actual factor

hqWeightedCNormOrder_of_stackRootUnitFactorOne:
  (∀ b, StackRootUnitFactorOne T b) -> HqWeightedCNormOrder T,
using S825 StackRootUnitFactorOne_iff_cNorm_eq_order (which uses the S817
actual stack root norm p^(-c_norm/(2l)) and its paper-norm factor).

hqWeightedCNormOrder_of_all_stackRootFactor_eq_one:
  (∀ b i, stackRootUnitFactor T b i = 1) -> HqWeightedCNormOrder T.

## Exact remaining

S894HqWeightedCNormOrderRequired := HqWeightedCNormOrder T.  Without the
per-b c_norm = order hypothesis it remains the exact Prop; no implication from
the finite sum to individual terms is asserted (weights may vanish).
