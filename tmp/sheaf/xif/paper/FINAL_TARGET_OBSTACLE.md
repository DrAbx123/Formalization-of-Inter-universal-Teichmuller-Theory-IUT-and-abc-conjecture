# Final target obstacle (ConcreteSourceComparisonObstacle)

## Target

  ConcreteSourceComparisonObstacle : Prop :=
    P.procession.average <= -concreteQLogVolume I

where
  concreteQLogVolume I = sourceQPilotSignedLog I.initial
  P.procession.average = signed theta average

Equivalent to:
  P.procession.average <= sourceBadQAbsLog I.initial

## Decisive audit

The target is NOT provable for arbitrary P, I.  There is an actual
counterexample theorem:

  not_concreteComparison_of_zero_badQAbsLog
    (hzero : sourceBadQAbsLog I.initial = 0)
    (havg : 0 < P.procession.average) :
    not (concreteSourceComparison O P)

so at zero bad-q absolute log the target is false.

## Paper hypotheses

In the paper, bad-place q-parameters and |log(q)| > 0 are part of the
input (Cor 3.12 excludes zero q).  The arbitrary-source formulation of the
obstacle lacks this restriction, so it is refutable in the current repo.

## What remains

After restricting to the paper source conditions, the only remaining
mathematical content is the single real estimate

  signed theta average <= source bad-q absolute log.

All intermediate qVFamilyK/Phi/tau alignments are irrelevant to this final
estimate.  No fake inequality is supplied.
