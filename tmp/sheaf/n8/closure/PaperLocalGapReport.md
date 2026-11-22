# Paper local gap report (Wave6, corrected Wave7)

Updated: 2026-10-24.  Scope: PaperN8Closure.lean and PaperC10Closure.lean only.
This is a gap inventory; no owner Lean file was edited in this update.

Correction: PaperC10Closure has been rebuilt against the current PaperN8Closure
olean.  Current PaperC10Closure.lean:
- lines 164, SHA256 02562e99451cebfeb9420a1026751bc1650287c644ecc07a887ed0f75832fe8c
- local sorry = 0
- thetaFiniteSource_nonempty and paperC10Output_nonempty are now actual
  theorems, not named gaps.
PaperN8Closure has exactly one local named gap: paperValuesBounded.
PaperQLeTheta is reduced and no longer local.

## 1. Local named gaps

| gap | file | kind | reducible? | source object? | note |
|---|---|---|---|---|---|
| paperValuesBounded | PaperN8Closure.lean | conclusion bound | no direct reduction | no | ValuesBounded for PaperC9Output; needs source-region/Theta tie |

Local count: 1 named gap.

PaperC10Closure local gaps: none.
- thetaFiniteSource_nonempty is actual via thetaFiniteSourceOfReadout.
- paperC10Output_nonempty is actual via PaperN8Closure.paperN8Closure_nonempty
  plus thetaFiniteSourceOfReadout.

## 2. External named gaps reachable from the two files

### PaperQLeThetaReduction (imported by PaperN8Closure)
| gap | kind | reducible? | source object? | note |
|---|---|---|---|---|
| missing_p6EllOutInValues | interface bridge | no | partially source | every P6 SourceAllowedOutput.ellOut lies in ValuesNamed; not derived from current defs |
| missing_paperC9Comparison | P6 conclusion | yes, alias implemented | no | same type/Q as C9PaperClosure.paperC9Comparison; see PaperC9ComparisonAlias.lean |

### C9PaperClosure (imported by PaperN8Closure)
| gap | kind | reducible? | source object? | note |
|---|---|---|---|---|
| paperC9Comparison | P6 conclusion | conditional | no | P6Exact/P6Epsilon for PaperC9Output.Q; could relate to route comparison after Q alignment |
| paperC9Output_nonempty | source existence | no | yes | actual PaperC9Output source record |

### C9QThetaValuesNamed (transitive through C9PaperClosure)
| gap | kind | reducible? | source object? | note |
|---|---|---|---|---|
| missing_q_source | source existence | no | yes | global Lq source object |
| missing_theta_source | source existence | no | yes | Theta source object |
| missing_values_source | source existence | no | yes | Values source object |

### N8RouteClosure (imported by PaperN8Closure)
| gap | kind | reducible? | source object? | note |
|---|---|---|---|---|
| p6HullSetup_nonempty | source existence | no | yes | actual P6HullSetup/R_alpha/U/H |
| p6ComparisonObligation | P6 conclusion | conditional | no | P6Exact/P6Epsilon for route chainA.Q; could use C9 paper comparison after Q alignment |

### P6 components (transitive through N8RouteClosure)
| gap | kind | reducible? | source object? | note |
|---|---|---|---|---|
| P6ChainA.globalLqDonor_nonempty | source existence | no | yes | global Lq donor |
| P6ChainB.missing_sl_to_complete_alpha | source existence | no | yes | S/L -> complete alpha |
| P6L.p6ReadoutExists_obligation | source existence | no | yes | global ell_out/P6Readout |
| P6Comparison.sourceAllowedOutput_nonempty | source existence | no | yes | actual source-allowed J |

External count: 13 named theorem-level gaps.

## 3. Reducible vs source object

Reducible or conditionally reducible:
- missing_paperC9Comparison: ALIAS IMPLEMENTED.  New file
  PaperC9ComparisonAlias.lean proves paperC9ComparisonAlias by direct call to
  C9PaperClosure.paperC9Comparison (same PaperC9Output O and same O.Q; no chainA
  alignment needed).  The upstream paperC9Comparison remains a named gap.
- paperC9Comparison and p6ComparisonObligation: conditionally reducible to one
  another after C9 Q/route Q alignment; no such alignment theorem exists yet.

Source objects (not reducible to current definitions):
- paperC9Output_nonempty
- missing_q_source, missing_theta_source, missing_values_source
- p6HullSetup_nonempty
- globalLqDonor_nonempty
- missing_sl_to_complete_alpha
- p6ReadoutExists_obligation
- sourceAllowedOutput_nonempty

Source/interface bridge:
- missing_p6EllOutInValues (P6 ellOut membership in Values), not a mere alias.

Conclusion gaps (not source objects):
- paperValuesBounded (ValuesBounded conclusion)
- paperC9Comparison / p6ComparisonObligation (P6 conclusions)
- missing_paperC9Comparison (now alias-reduced by PaperC9ComparisonAlias.lean)

## 4. PaperC10Closure status

Current PaperC10Closure.lean has:
- local sorry = 0;
- thetaFiniteSource_nonempty actual (thetaFiniteSourceOfReadout);
- paperC10Output_nonempty actual (uses PaperN8Closure.paperN8Closure_nonempty);
- PaperC10Output and PaperC10Conclusion compile against the corrected
  PaperN8Output API (p6RouteObligations/c9 derived q/theta/values);
- no Q<=Theta input: paperC10Conclusion uses PaperN8Closure.paperQ_le_theta.

PaperC10Closure is no longer a stale-API blocker.  Its proof depends on the
same external named gaps as PaperN8Closure plus paperValuesBounded; it is not
target_accepted/kernel_closed.

## 5. Counts and classification

Local: 1 (paperValuesBounded only).
External: 13.
Reducible/conditionally reducible: 3
(missing_paperC9Comparison alias implemented; paperC9Comparison/
p6ComparisonObligation conditional pair).
Source objects: 9
(paperC9Output_nonempty, missing_q/theta/values, p6HullSetup_nonempty,
globalLqDonor_nonempty, missing_sl_to_complete_alpha,
p6ReadoutExists_obligation, sourceAllowedOutput_nonempty).
Conclusion/interface gaps: paperValuesBounded, missing_p6EllOutInValues, and the
P6 comparison gaps (paperC9Comparison/p6ComparisonObligation).

No target_accepted, kernel_closed, or Project build claim.  No ABC/old layer.
