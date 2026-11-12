# LEAD MEMO — durable operating rules

Date: 2026-10-24. Owner: Lead. Read this before every dispatch batch.

## 1. Event-driven dispatch

- Do NOT wait for a whole batch to finish.
- When any agent returns: collect result, compile it, assign the next ready task in the same turn.
- Keep all idle agents assigned; only wait when the next task truly depends on another agent's output.

## 2. High-value gate (no chicken tasks)

Only dispatch a task that has at least one of:
1. an actual construction path from existing production/source objects;
2. a decisive no-go that forces a target correction;
3. an exact target correction with clear consumer impact.

Reject: repeated searches, duplicate no-gos, vague 'try to prove X', arbitrary-interface attempts.

## 3. Target-class guard

- legacy closure and old Layer0/Layer1 closures are NOT paper N8 closure.
- old layers only as donors when the current N8 route consumes them through an explicit adapter.
- never report/consume legacy as paper target; see CLOSURE-GUARD.md.

## 4. Sorry policy

- named theorem-level sorry is allowed and expected.
- do NOT pursue no-sorry by weakening targets or faking objects.
- each named gap must be exact-type and have a consumer.

## 5. One DAG / verification

Every new file must be attached to a DAG node/evidence and have central compile status. Agent exit0 is not central verification.

## 6. Dispatch checklist (run before sending)

- [ ] Which target node/consumer does this task affect?
- [ ] Is it actual / decisive no-go / target correction?
- [ ] Does it reuse existing files instead of re-searching?
- [ ] Is the write scope disjoint from other owners?
- [ ] What is the exact expected output (declarations, named gaps, hash)?

## 7. If the user corrects a workflow rule

Immediately write it here (not only in STATE/chat), then apply it to the next dispatch. Do not require the user to repeat it.

## 8. Target changes (2026-10-24)

- User may authorize a target correction; record it in coord/TARGET-CHANGE-*.md, reopen affected nodes, and preserve the final destination strength.
- A target correction is NOT permission to weaken Q/Theta/Values or use vacuous/underconstrained donors.
