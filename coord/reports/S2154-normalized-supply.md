# S2154: normalized generator supply audit

Date: 2026-11-02. Layer O; consumer S2144/S2139 root coefficient scaling data.

## Actual existing

QVFamNormalizedGeneratorSupplyActual constructs, unconditionally:

- qVFamNormalizedGenerator : CommonPrimeCompletion at the tensor place;
- qVFamNormalizedCoefficient = -logb_p ||q||_normalized;
- qVFamNormalizedGenerator_norm:
    ||q|| = p^(-c_norm);
- qVFamNormalizedCoefficient_pos;
- qVFamNormalizedPureFractionalScalingData at c_norm;
- qVFamNormalizedGeneratorSupply_of_coefficient_eq:
    c_norm = qVFamPureCoefficient -> NormalizedGeneratorSupply.

## New Lean

tmp/sheaf/xif/paper/S2154NormalizedSupplyActual.lean
SHA256 EF2FD66CE5AF3EBA408A62E53D7C710F178463650660B88E6C37F70979FB50ED
EXIT=0
olean SHA256 290B31DD6D76F2077D1527D428FBFE43B5DF2197218BEFFEC4AAED7B3CB9B1DE
size 84488
axioms propext, Classical.choice, Quot.sound.

Contents:
- s2154CoefficientGap := QVFamNormalizedCoefficientGap;
- s2154NormalizedGeneratorSupply_of_coefficientGap;
- s2154GeneratorAt c: actual generator in CommonPrimeCompletion with
  norm p^(-c);
- s2154GeneratorAtNormalized at c_norm;
- s2154RootCoefficientSupplyMissing:
    Nonempty (s2154GeneratorAt (qVFamPaperRootCoefficient)).

## Exact first missing

Two distinct gaps, not to be conflated:

1. NormalizedGeneratorSupply T b at the default-norm qVFamPureCoefficient is
   conditional on
     QVFamNormalizedCoefficientGap :
       qVFamNormalizedCoefficient = qVFamPureCoefficient.
   The tree has only integer-ball norm equivalences, not equality of the
   default and normalized norms on the qVFamily element.

2. The actual root coefficient supply needed by S2144/S2139 is
     Nonempty (s2154GeneratorAt (qVFamPaperRootCoefficient)),
   i.e. a CommonPrimeCompletion generator of norm
     p^(-(order(qVFamily)/(2l))).
   Existing qVFamNormalizedGenerator has norm p^(-c_norm) with c_norm = order,
   not order/(2l).  A 2l-th root in the completion is not available (S342), so
   this is not derivable from the normalized generator.

No inhabitant of either gap is asserted.

## Conclusion

- BUILT: conditional NormalizedGeneratorSupply from coefficient gap; actual
  normalized generator at c_norm; exact arbitrary-coefficient supply shape.
- MISSING: QVFamNormalizedCoefficientGap for the default coefficient, and
  root-coefficient normalized generator supply.
- no fake; no S2040 assumption.
