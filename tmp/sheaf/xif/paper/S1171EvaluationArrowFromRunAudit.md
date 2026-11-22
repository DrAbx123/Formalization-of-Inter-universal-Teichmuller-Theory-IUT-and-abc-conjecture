# S1171: evaluation arrow from an actual SourceRun operation

Read: S1164OperationArrowActual.lean, S1170RouteTraceAuditActual.lean,
S1158ConcreteSquareAttempt.md, SourceH1H2Construction.

## 1. S1164 actual part

S1164OperationArrowActual builds four candidate F-prime-strip arrows from
actual source data:

  lowerEnv    = I.fLinkAt 0 0 0 1 : (0,0) -> (0,1)
  verticalEnv = I.fLinkAt 0 0 1 0 : (0,0) -> (1,0)
  verticalGau = I.fLinkAt 0 1 1 1 : (0,1) -> (1,1)
  upperEnv    = I.fLinkAt 1 0 1 1 : (1,0) -> (1,1)

and proves commEnv by fLinkAt_trans (S1164CommEnv).

Thus the four arrows and commEnv are actual, but they are F-link arrows, not
yet evaluations produced by a source run operation.

## 2. S1170 actual part

S1170RouteTraceAuditActual provides an actual route trace for
ParametricCarrier.AlgorithmInput:

  routeTrace carrier route source
  routeTrace_endpoint_eq_routeTarget
  routeTrace_endpoint_eq_runAlgorithm_target
  routeTraceForgetRun_eq_runAlgorithm_target

This trace is a trace of `Choice`, controlled by `carrier.core.applyStep` and
the route list.  It records the endpoint of runAlgorithm.

## 3. Missing SourceRun / operation API

Grep over `LeanFormal` finds no declaration named `SourceRun`, `runOperation`, or
`fromRunOperation`.  S1170 is the closest actual run layer, but it lives at the
ParametricCarrier Label/Choice level, not at the F-prime-strip level needed by
S1164ActualEvaluationArrow.

In particular there is no actual map

  run operation -> FPrimeStripEquiv (I.fPrimeStripAt 1 0) (I.fPrimeStripAt 1 1)

and no provenance theorem that `s1164UpperEnv` is produced by such a run.
`S1164ActualEvaluationArrow.fromRunOperation` therefore remains an unproved
proposition; it cannot be inhabited without adding the missing source-run
operation API.

## 4. First exact source operation sublemma

The first exact missing datum is a source-run operation whose result is an
F-prime-strip equivalence, together with provenance:

  structure S1171SourceOperationEvaluation where
    Run : Type
    run : Run
    upperEnv : FPrimeStripEquiv (I.fPrimeStripAt 1 0) (I.fPrimeStripAt 1 1)
    run_produces_upperEnv : Prop
    run_provenance : run_produces_upperEnv

and the matching three arrows/commEnv produced by the same run.  This is an
exact obligation, not a definitional consequence of routeTrace: S1170's trace
does not construct F-prime-strip arrows.

Equivalently, the missing sublemma is:

  S1171SourceRunOperationRequired : Prop :=
    Nonempty (S1171SourceOperationEvaluation I)

with no inhabitant asserted.

## 5. What can be proved without the missing operation

Actual: S1164's four candidate arrows and commEnv; S1170's routeTrace and its
endpoint/runAlgorithm target identities.

Not actual: that these arrows come from a SourceRun operation.  The first gap is
the source operation itself, not the F-link commutation and not routeTrace.

## Verdict

- actual: candidate four arrows + commEnv (S1164); routeTrace API (S1170).
- exact: S1171SourceOperationEvaluation / S1171SourceRunOperationRequired.
- no fake fromRunOperation, no True inhabitant, no wrapper of S1073.
