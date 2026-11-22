# N8 paper closure report (Wave4)

Updated: 2026-10-24.  Scope: current paper N8 route only.  ABC/Cor312 and the
old Layer0/Layer1 closures are OUT OF SCOPE.  Legacy N8FullOutput, the old
N8Closure.lean C0 assembly, N8ClosureAchieved legacy named assembly and the old
C10 closure are NOT part of this route.

Status class: paper-route named-sorry closure, audit-corrected.
target_accepted: NO.  kernel_closed: NO.  Project build: not run.

## 1. Centrally compiled paper-route components

Wave1 (central EXIT=0 recorded in coord/PAPER-N8-CLOSURE.md; logs are warning
only, no exit code stored):
- C3T11NamedClosure.lean
- P6Bridge.lean
- C6C7C8NamedClosure.lean
- P6SHEIndClosure.lean
- P6LClosure.lean
- C9QThetaValuesNamed.lean
- N8RouteClosure.lean
- C9P6Closure.lean

Wave2 (central EXIT=0 recorded in coord/PAPER-N8-CLOSURE.md):
- C9PaperClosure.lean
- PaperN8Closure.lean
- P6BridgeActual.lean
- P6LActual.lean
- P6HullActual.lean
- P6TensorActual.lean
- P6APTActual.lean
- C7C8ActualAttempt.lean

Wave3/4 current source hashes (this audit):
- N8RouteClosure.lean: lines=103 SHA256=248557df33529c3381c4fe2b19594bd39db5da87d5b03dfcfe7e18c597cdec1c; two local named sorries.
- C9PaperClosure.lean: lines=161 SHA256=7f9680ee48c43d185e526860ddcd5d9f0614378e1bd5942418b79893f0d4dbe5; two named sorries (paperC9Comparison, paperC9Output_nonempty); comparison removed from PaperC9Output.
- PaperN8Closure.lean: lines=138 SHA256=2d9086f62bf505765eb0d1ad8250d5593a08bcb3bca1d4428b678924b3ef928d; exit0; two local named sorries.
- PaperC10Closure.lean: lines=160 SHA256=828d191c8a028a0cb5c1b6ff3a3dc513449f543572fd3f3ac231269191231872; two named sorries (see section 3 for stale-build finding).

Warning: central "EXIT=0" entries for Wave1/2 are recorded from agent runs; this
Wave4 audit did not rerun all of them and does not establish kernel closure.

## 2. PaperN8Output status

Current PaperN8Closure.PaperN8Output fields:
- p6RouteObligations : N8RouteClosure.N8RouteObligations X mu
- c9 : C9PaperClosure.PaperC9Output X mu

There are no stored q/theta/values fields and no valuesBounded/q_le_theta fields.
They are derived/defined:
- PaperN8Output.q := c9.Q
- PaperN8Output.theta := c9.Theta
- PaperN8Output.values := c9.valuesSet
- PaperN8Output.q_eq_nativeScalar (proved)
- PaperN8Output.q_eq_route (proved to p6RouteObligations.chainA.Q)

Separate conclusion theorems:
- paperValuesBounded (X mu C) : C9PaperClosure.ValuesBounded C := by sorry
- paperQLeTheta (X mu C) : C9PaperClosure.QInRleqTheta C := by sorry
- paperQ_le_theta (X mu O) : O.q <= O.theta — proved from paperQLeTheta via
  C9PaperClosure.qInRleqTheta_iff
- paperN8Closure_nonempty (X ...) : Nonempty (PaperN8Output X mu) — assembles
  p6RouteObligations from n8RouteObligations_nonempty and c9 from
  C9PaperClosure.paperC9Output_nonempty.

p6RouteObligations is a P6 obligation package, NOT a constructed source closure:
- chainB is P6ChainB.MissingSLToCompleteAlpha (a Prop), not actual
  CompleteAlpha/R_alpha;
- hull is an abstract P6Hull.P6HullSetup filled by p6HullSetup_nonempty;
- comparison is P6Exact or P6Epsilon over SourceAllowedOutput X, independent of
  Q<=Theta.

J range: J is P6Comparison.SourceAllowedOutput X.  No Set-of-Type J range is
defined in PaperN8Closure now.  Q<=Theta is only a conclusion, never a P6 input.

PaperN8Output residual alignment gap: c9.Theta (from PaperC9Output.theta) and
p6RouteObligations.readout are two separate P6Readout values; the current
structure does not require them to be the same source readout.  PaperC10 needs
that alignment.  Exact correction suggestion: add a named source-alignment lemma
c9Theta_eq_routeReadout (O) : O.c9.theta = O.p6RouteObligations.readout := by
sorry, or make c9 consume the route readout directly.

## 3. PaperC10 status and stale-build finding

File exists: PaperC10Closure.lean, lines=160,
SHA256=828d191c8a028a0cb5c1b6ff3a3dc513449f543572fd3f3ac231269191231872.
It defines ThetaFiniteSource, PaperC10Output, PaperC10Conclusion,
PaperC10JRange and two named sorries:
- thetaFiniteSource_nonempty
- paperC10Output_nonempty

Audit finding: the current PaperC10Closure source was written against the
previous PaperN8Output API and currently compiles only against a STALE
PaperN8Closure.olean.
Evidence:
- .lake/build/lib/lean/tmp/sheaf/n8/closure/PaperN8Closure.olean mtime
  2026-10-23T23:17:52, while current PaperN8Closure.lean mtime
  2026-10-23T23:20:04;
- PaperC10Closure source refers to n8.route.readout, n8.theta_eq and
  n8.q_le_theta, but the corrected PaperN8Output has p6RouteObligations, derived
  theta, and no q_le_theta field.

Therefore the current PaperC10 "exit0" is not evidence against the corrected
PaperN8 API.  Exact corrections needed by the PaperC10 owner (do not edit here):
1. n8.route.readout -> n8.p6RouteObligations.readout.
2. Replace n8.theta_eq use by the derived PaperN8Output.theta (and add the
   c9Theta_eq_routeReadout alignment gap suggested in section 2).
3. Replace n8.q_le_theta field use by theorem paperQ_le_theta applied to n8.
4. Rebuild the current PaperN8Closure olean centrally, then recompile
   PaperC10Closure; do not rely on the stale olean.
5. Keep PaperC10JRange as Set (SourceAllowedOutput X) = Set.univ; no Set-of-Type
   range.

## 4. Exact named gaps still open

PaperN8Closure local:
- paperValuesBounded
- paperQLeTheta

N8RouteClosure/P6 route:
- p6HullSetup_nonempty
- p6ComparisonObligation
- P6ChainA.globalLqDonor_nonempty
- P6ChainB.missing_sl_to_complete_alpha
- P6L.p6ReadoutExists_obligation
- P6Comparison.sourceAllowedOutput_nonempty

C9 source:
- C9PaperClosure.paperC9Comparison
- C9PaperClosure.paperC9Output_nonempty
- C9QThetaValuesNamed.missing_q_source / missing_theta_source /
  missing_values_source (transitively used source-object existence)

PaperC10:
- thetaFiniteSource_nonempty
- paperC10Output_nonempty
- plus the PaperN8 c9/route readout alignment gap listed in section 2.

## 5. Next actual attempts (paper route only)

1. Rebuild current PaperN8Closure olean centrally and recompile PaperC10Closure
   against it; fix the three field-name/API mismatches listed in section 3.
2. Add the c9Theta_eq_routeReadout exact alignment gap or consume route.readout
   in PaperC9Output; this is needed before PaperC10 finite-Theta semantics can be
   real.
3. Replace P6ChainB.MissingSLToCompleteAlpha Prop with actual CompleteAlpha/
   R_alpha data, and instantiate P6HullSetup from actual source U/H; then
   p6RouteObligations may be called a source closure.
4. Tie Theta/Values to actual source objects (C4 output regions / C9Paper
   thetaHull), not only the abstract P6Readout donor.
5. Keep Q<=Theta as a conclusion; do not feed it into P6 comparison.
6. No ABC/old-layer work in this route.

## 6. Status summary

PaperN8Output: audit-corrected data structure + component derivations; local two
named conclusion gaps; compiles exit0.  PaperC10Closure: source present but
stale relative to PaperN8Closure; current green is not valid for the corrected
API.  Paper-route named-sorry closure remains open.  No target_accepted, no
kernel_closed, no Project build.

## Wave4 central compile (2026-10-24)

- PaperC10Closure SHA C02D5EB1710C346DB4A5DB0D34ECEDA0E38DCBD850D343AAA0E9E43009D0D297, central exit0; 3 named gaps c9Theta_eq_routeReadout/thetaFiniteSource_nonempty/paperC10Output_nonempty.
- P6AdmActualAttempt central exit0; actual H-admissibility interface, not full Stp4.
- PaperQLeThetaReduction central exit0; conditional Q<=Theta from comparison + ValuesBounded + P6EllOutInValues, with named gaps missing_p6EllOutInValues/missing_paperC9Comparison.
- PaperC10Conclusion proved from paperQ_le_theta + explicit Theta finite source.
- Stale-olean issue fixed by rebuilding PaperN8Closure/C9PaperClosure oleans.
