# S1547: residue norm base reduction for S1087CoeffLe

Date: 2026-10-31. EXIT=0; exact first number-theory lemma retained.

## Exact first missing lemma

S1547ResidueNormBaseEqPrime (T b):
  residueNormBase (comap (k := Q) (qVFamTensorPlace T b)) = qVFamTensorP T b.

This is the number-theory statement that the rational place below the actual
F-place has residue norm equal to its rational prime.  It is not assumed; it is
recorded as the exact first lemma.

## Conditional actual reduction

Using ArithmeticQPilotBaseChange.residueNormBase_eq_lower_pow and
localResidueDegree_pos:

  s1547ResidueLogRatio_of_residueNormBase :
    S1547ResidueNormBaseEqPrime -> S1526ResidueLogRatioGeOne

The proof rewrites residueNormBase(F-place)^localResidueDegree, uses the exact
lower equality, and cancels log(p), leaving localResidueDegree >= 1.

  s1547CoeffLe_of_residueNormBase :
    S1547ResidueNormBaseEqPrime -> S1087CoeffLe

via S1526.s1526CoeffLe_of_residueLogRatio.

No fake equality, no assumption of p=...; the lower-place equality remains the
exact missing number-theory computation.

## Verification

EXIT=0; olean generated.
