# S724: QVFamBlockMapsFractionalLattice direct proof attempt / exact goal

Date: 2026-10-30. Exact obstruction; no fake proof.

## Proved

qVFamBlockLinearEquiv_tprod:
  qVFamBlockLinearEquiv (finitePadicTensorTprod f) = f ().

This uses qVFamBlockLinearEquiv = PiTensorProduct.subsingletonEquiv and
PiTensorProduct.subsingletonEquiv_apply_tprod.

## Exact target

QVFamBlockMapsFractionalLatticeGoal T b c :=
  forall x in arithmeticTupleFractionalLattice c,
    qVFamBlockLinearEquiv x in padicFractionalLattice (sum c).

S724ExactGoal records it; no inhabitant.

## Exact blockers

1. Type alignment:
   f () : CommonPrimeCompletion (qVFamTensorPlaces T b () ())
   but padicFractionalLattice is over rootBase T b = NormalizedCompletion (...).
   These are type synonyms but local instances differ; simpa leaves the
   membership at CommonPrimeCompletion, expected at rootBase.

2. Scalar action in Submodule.span_induction:
   qVFamBlockLinearEquiv (z • a) = (z : Q_p) • qVFamBlockLinearEquiv a
   for z : Z_p.  Direct rewrite via Algebra.smul_def fails because the
   scalar action on the tensor block is the Z_p action and the coercion
   (z : Q_p) is not the expected one.  The needed compatible-smul/scalar
   tower instance is not found:
   LinearMap.CompatibleSMul (qVFamTensorBlock T b) (rootBase T b) Z_p Q_p.

3. Submodule.span_induction order: signature is mem, zero, add, smul;
   add/smul require induction hypotheses after membership proofs.

## Consequence

No unconditional proof is appended. Remaining exact work:
* prove the rootBase/CommonPrimeCompletion instance alignment (or cast the
  pure tensor membership along the normalized-completion type equality);
* prove the Z_p scalar compatibility for qVFamBlockLinearEquiv;
* run span induction on arithmeticTupleFractionalLattice.
