# S546: qHalf root candidate and mu_2l ratio

Date: 2026-10-29. Algebraic-closure qHalf candidate; no completion root asserted.

## qHalf candidate

qHalfRoot parameter : (AlgebraicClosure (Completion place))^x
  := Classical.choose (exists_twoLRoot_unit_in_algebraicClosure parameter).

qHalfRoot_pow:
  qHalfRoot^(2l) = tateParameterUnit place parameter.q parameter.q_ne_zero.

QHalfCandidate packages root and root_pow; qHalfCandidate is the actual instance.

## mu_2l ratios

qHalfRoot_ratio_mem_rootsOfUnity:
  if r1,r2 are algebraic-closure units with r_i^(2l)=tateParameterUnit q,
  then r1/r2 ∈ rootsOfUnity (2l) (AlgebraicClosure (Completion place)).

completionRoot_ratio_mem_rootsOfUnity:
  completion-unit wrapper of the old repository theorem
  qParameterTwoLRootUnit_ratio_mem_rootsOfUnity.

No completion 2l-root existence is asserted; only the algebraic-closure root
and conditional completion ratio.  No fake root, no L.
