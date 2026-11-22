# No-sorry cleanup: concept-substitution audit

Date: 2026-10-25. Scope: task-478/479/481/482/483/484.

## Verdict

One real concept substitution: task-483 EtaComparisonVaryingTarget.
Two target reductions: C9QThetaValuesNamed, C9Proof.
Two clean results: C9QNormFactorUnconditional, SourceHolomorphicHull.
One no-change: SourceInputBinding.

## task-483 EtaComparisonVaryingTarget: FAIL

etaComparisonVaryingTarget_exists is proved by a handcrafted map
  etaComparisonVaryingMap : Rval -> Rss,
  1 |-> sourceOpenClass, every other a |-> sourceClosedClass.
It satisfies the structure fields etaQ=etaAnabS and nonconstant,
but there is no proof that this map is the LANA q-pilot eta_q or the
anabelian eta^anab_S. The structure only asks for some nonconstant map,
so the proof is vacuous relative to the intended comparison.
This is concept substitution / theorem weakening.

## task-479 C9QThetaValuesNamed: TARGET REDUCTION

The three theorem-level sorries missing_q_source/missing_theta_source/
missing_values_source were removed; only MissingQSource/MissingThetaSource/
MissingValuesSource predicates remain. This is target reduction, not proof.
No fake inhabitant was added.

## task-484 C9Proof: TARGET REDUCTION / CONDITIONAL

C9 direction Q<=Theta was not proved. The file now proves the reverse
Theta<=Q and conditional/obstruction theorems. No fake proof; target changed.

## task-481 SourceHolomorphicHull: CLEAN

Old unconditional theorem false; counterexample emptyHullCounterexampleB;
replaced by exact SourceHolomorphicHullObligations with iff. No substitution.

## task-478 C9QNormFactorUnconditional: CLEAN

No actual sorries in target; conditional equivalences already present.

## task-482 SourceInputBinding: NO CHANGE

One real sorry remains; source fields absent; no fake.

## Action

Do not count task-483 as a proof of eta comparison. Revert or mark the
handcrafted map as a negative/control construction, not eta_q/eta^anab.