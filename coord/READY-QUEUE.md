# Ready queue (event-driven dispatch)

Date 2026-10-24. User correction: do not wait for the whole batch; when any agent returns, immediately assign the next ready task.

## Rule

- Keep all idle agents assigned.
- Maintain a ready backlog; pop one task per returned agent within the same turn when possible.
- Do not batch-wait unless the next task depends on another agent's output.
- Record each assignment and result; central compile in parallel.

## Current Wave6 (all 8 busy)

| owner | file | target |
|---|---|---|
| multiradial | PaperValuesBoundedAttempt.lean | prove/reduce paperValuesBounded or exact no-go |
| primespine | PaperLocalGapReport.md | local vs external named gaps |
| transport | PaperC9ComparisonAttempt.lean | derive paperC9Comparison from route |
| qside | C4ExistenceAttempt.lean | C4 actual existence/no-go |
| kummer | C3QPacketIdentificationAttempt.lean | q packet identification actual/no-go |
| iplsheapt | P6PermittedActualAttempt.lean | permitted actual/no-go |
| volumedet | P6HullStp4Attempt.lean | Stp4 Adm_out attempt/no-go |
| logdescent | P6ReadoutFromActualAttempt.lean | P6Readout actual/no-go |

## Backlog (assign on each return)

1. Reduce PaperN8Closure.paperValuesBounded via same-source Values/Theta readout.
2. Reduce C9PaperClosure.paperC9Comparison via route comparison + chainA alignment.
3. Close C10 local gaps if PaperN8 local gaps reduce.
4. P6ChainB actual CompleteAlpha/R_alpha attempt.
5. P6Hull actual Stp4 donor follow-up.
6. P6Tensor actual landing follow-up.
7. C1 contract/index donor follow-up.
8. C7 U2IQ / C8 Ob3-3 actual attempt.

## Central compile

Compile each new file on return; do not wait for all.

## Wave17 (resumed parallel, compliance-aware)

- multiradial: PaperN8ReadoutBoundSource.lean
- primespine: C1OldStripMonCanonical.lean
- transport: P6TensorGlobalAdmConstruction.lean
- qside: C1OldStripMonCanonicalConsumer.lean
- kummer: C3TensorCanonicalLanding.lean
- iplsheapt: P6IndEvalCompatFromLabelAction.lean
- volumedet: C7ThetaUnitHullActual.lean
- logdescent: P6WeightedTupleIndexBridge.lean

Rules: exact named/new proof, no free field, compile exit0, report declaration/hash/consumer; Lead updates DAG/registry; central audit chain continues.

## Wave18 high-value only (2026-10-24)

Low-yield Wave17 searches interrupted. New rule: no task accepted unless it has (a) an actual construction path, (b) a decisive no-go/target correction, or (c) closes a named gap with a transparent consumer. Pure re-search/duplicate no-go is rejected.

- primespine: C1ActualSourceInput (actual source input or target correction)
- qside: C1ActualInputQuotientConsumer
- transport: P6NonarchAdmActual
- kummer: C3TensorTargetCorrection
- iplsheapt: C4ActualOutputFromSource
- volumedet: C7ThetaUnitHullFinal
- logdescent: P6ArchimedeanAdmNoGo (decisive)
- multiradial: C10PaperFinalAssembly

## Mandatory memo

Before every dispatch, read and apply `coord/LEAD-MEMO.md` (event-driven, high-value gate, target-class guard).
