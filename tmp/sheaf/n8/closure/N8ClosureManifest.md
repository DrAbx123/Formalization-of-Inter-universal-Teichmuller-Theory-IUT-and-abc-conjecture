# N8 current-route closure manifest

Updated: 2026-10-24. Scope: current N8 route only (C0-C10, P0-P7, T11/T10/T8,
legacy C10 named closure).  ABC/Cor312 and old Layer0/Layer1 work are out of
scope for this manifest.

Status source: dag/nodes/*.json, inventory only.  This file does not re-run
builds or reclassify nodes into closure.  Abbreviations:

- SC: statement_compiles recorded in the node
- NS: named sorry / named obligation count
- Donor: reusable actual interface donor (not a closure claim)
- Off: off-route, superseded, legacy, or false/no-go target

No node here is target_accepted.  No comparator/project build was run for this
manifest.

## 1. Main N8 route nodes

| node | route role | SC | NS | Donor | Off | evidence / next |
|---|---|---:|---:|---:|---:|---|
| n8-c0-target-signature | old C0 target signature | yes | 1 | no | yes | TargetSignature; C0 target audited false/overstrong; use native C0 instead |
| n8-c1-source-input-binding | C1 old source binding | yes | 1 | no | no | SourceInputBinding.lean exit0; placeEquiv/R/fiber donor open |
| n8-c2-source-log-kummer | C2 old log-Kummer | yes | 1 | partial | no | C2Actual finite-place donor exists; full C2 named gap |
| n8-c3-source-pilot-region | C3 old pilot region | yes | 1 | no | no | SourcePilotRegion.lean exit0; q/tensor/root donor gaps |
| n8-c4-source-witnessed-output | C4 actual output interface | yes | 0 | yes | no | SourceWitnessedOutput.lean exit0; IndAction G2/G3 open |
| n8-c5-algorithm-compatibility | C5 old algorithm compatibility | yes | 1 | partial | no | SourceAlgorithmCompatibility exit0; APT/permitted open |
| n8-c6-actual-iq-data | C6 actual IQ data | yes | 0 | yes | no | C6ActualIQData + IsActual; reusable donor |
| n8-c7-holomorphic-hull | C7 actual IQ hull | yes | 1 | no | no | SourceHolomorphicHull exit0; hull existence named gap |
| n8-c8-degree-comparison-iq | C8 IQ degree comparison | yes | 0* | partial | no | proof body checked; semantic named_sorry_open (*theorems use named sorry) |
| n8-c9-pilot-approximation-iq | old C9 IQ approximation | yes | 1 | no | yes | superseded by C9 route/P0-P7; not current Values/Q target |
| n8-c10-assembly | actual old C10 assembly | yes | 0 | partial | yes | N8Closure.lean assembly; legacy C0/C1 dependency, not paper closure |
| n8-t8-iq-carrier | T8 IQ carrier | yes | 0 | yes | no | IQCarrier.lean exit0; reusable donor |
| n8-t10-ipl-family | T10 IPL family | yes | 1 | no | no | IPLFamilyData exit0; family existence named gap |
| n8-t11-theta-to-iq | T11 theta -> IQ | yes | 1 | no | no | SourceThetaToIQ exit0; T11 obligation named gap |
| n8-s3-t11 | S3 T11 actual interface | partial | 0 | yes | no | T11Actual; zero-sorry residual packet identification, target pending |
| n8-s3-t11-packet | T11 packet identification | no | 0 | no | yes | no_go/blocked_no_donor; not current T11 interface |
| n8-c10-named-assembly | legacy C10 named closure | yes | 10 | no | yes | N8ClosureAchieved; legacy archived scaffold, not paper closure |

Notes:
- The C0 target is off-route: C0Base.lean records the unconditional source-hull
  finiteness contradiction and corrected boundary.
- The old C9 IQ approximation node is off-route; current Values/Q work is
  P0-P7 plus P6ChainA/P6ChainB/P6Hull/P6L/P6Comparison.
- The legacy C10 named closure is archived evidence, not the current paper route.

## 2. P0-P7 route nodes

| node | stage | proof_status | NS | gaps | classification |
|---|---|---|---:|---:|---|
| n8-c9-p0 | in_progress | not_started | 0 | 3 | gap; target revision pending |
| n8-c9-p1 | in_progress | not_started | 0 | 3 | gap; full output/alpha construction |
| n8-c9-p2 | in_progress | not_started | 0 | 1 | gap; single blocking object (readout/normalization) |
| n8-c9-p3 | in_progress | not_started | 0 | 1 | gap; hull/finite-volume package |
| n8-c9-p4 | in_progress | not_started | 0 | 1 | gap; HullPoss/Values boundedness |
| n8-c9-p5 | in_progress | not_started | 0 | 1 | gap; Kummer/degree calibration |
| n8-c9-p6 | in_progress | not_started | 0 | 4 | gap; double-construction comparison |
| n8-c9-p7 | in_progress | not_started | 0 | 1 | gap; numerical Q<=Theta closure |
| n8-c9-output-region-source-route | open | documented gaps | 0 | 0 | route record only; corrected object refinement required |

All P0-P7 statements are not locked; none is statement_compiles yet.

## 3. Code-level route artifacts (not DAG replacements)

| artifact | role | status | named gaps |
|---|---|---|---|
| tmp/sheaf/n8/closure/P6ChainA.lean | native q -> local q-pilot -> L_q -> Q | exit0 | GlobalLqDonor existence |
| tmp/sheaf/n8/closure/P6ChainB.lean | S/L -> complete alpha -> R_alpha/U/H | exit0 | missing_sl_to_complete_alpha |
| tmp/sheaf/n8/closure/P6Hull.lean | paper hull/HullPoss package | exit0 | abstract setup; source instantiation separate |
| tmp/sheaf/n8/closure/P6L.lean | global signed ell_out/Adm/P6Readout | exit0 | p6ReadoutExists_obligation |
| tmp/sheaf/n8/closure/P6Comparison.lean | exact/epsilon P6, J independent of Q | exit0 | sourceAllowedOutput_nonempty |
| tmp/sheaf/n8/closure/N8RouteClosure.lean | assembles the five P6 components into N8RouteObligations | exit0 | p6HullSetup_nonempty, p6ComparisonObligation + imported P6ChainA/B/L gaps |
| tmp/sheaf/n8/closure/C9P6Closure.lean | prior assembly of P6 components | exit0 record | p6SourceClosure_nonempty |

N8RouteClosure.lean uses no ABC/Cor312 import and no Q<=Theta input.  Its
N8RouteObligations fields are: chainA, chainB, hull, readout, comparison; the
comparison field is P6Exact or P6Epsilon.

## 4. Easy-first list

1. Reuse closed actual donors: C6ActualIQData (.IsActual), T8 IQCarrier, C4
   SourceWitnessedOutput, C2Actual finite-place local shell.  These are donor
   interfaces, not end-to-end closure.
2. Use C8 proof body as an interface (named degree comparison remains); do not
   count it as closed.
3. Single-named-gap nodes C1, C2(full), C3, C5(full), C7, T10, T11: replace one
   named donor at a time, starting with the native place/root/tensor donors that
   are already available in NativeC1/NativeC3/C3Roots.
4. P2/P3/P4/P5/P7 have one recorded gap each; P0/P1/P6 have multiple gaps.  Do
   not start P6 closure before ChainA/B readout and HullPoss objects are stated.
5. Keep C0 old target and legacy C10 named assembly off-route.  C0Base no-go and
   the corrected boundary remain the reference for old C0.
6. Preserve the current P6 route files as the only active Q/Values/Theta chain;
   old C9 IQ approximation is off-route.

## 5. Current counts

Main N8 route table: 17 nodes.
P0-P7 table: 8 nodes + 1 route record.
Code-level artifacts: 7 active files.
Counts by main marker:

- statement_compiles recorded: C0(old), C1, C2, C3, C5, C7, C8, C9(old),
  T10, T11, legacy C10 (some also named/off-route).
- named component gaps: C0(1), C1(1), C2(1), C3(1), C5(1), C7(1), C8(semantic),
  C9(1), T10(1), T11(1), legacy C10(10), plus P6 route gaps.
- reusable actual donors: C4, C6, T8, partial C2, partial C8.
- off-route: old C0 target, old C9 IQ approximation, old C10 assembly/legacy
  named closure, S3 no-go leaves, T11 packet no-go.

No N8 paper closure is claimed.  Current route remains open at C1-C3/C5/C7/C9
native donors and P0-P7/P6 components.


## 6. Wave1/Wave2 paper-route compile inventory

This section is audit metadata from central compile logs, not a new build.  A log
with warnings only is listed as "central log warnings"; exit codes are not stored
in those logs.  Empty logs mean no diagnostics were recorded, not kernel closure.

Wave1:
- C3T11NamedClosure.lean: wave1 log warning, one named sorry at line77.
- C6C7C8NamedClosure.lean: wave1 log empty (no diagnostics recorded).
- C9P6Closure.lean: wave1 log warning, one named sorry at line121.
- C9QThetaValuesNamed.lean: wave1 log warnings, three named sorries (lines87/93/99).
- N8RouteClosure.lean: wave1 log warnings, two named sorries (lines50/57).
- P6Bridge.lean: wave1 log warning, one named sorry at line70.
- P6LClosure.lean: wave1 log warnings, one named sorry at line51.
- P6SHEIndClosure.lean: wave1 log empty (no diagnostics recorded).

Wave2:
- C9PaperClosure.lean: wave2 log warning, one named sorry at line140.
- P6BridgeActual.lean: one named sorry at line70.
- P6HullActual.lean: one named sorry at line84.
- P6LActual.lean: one named sorry at line61.
- P6TensorActual.lean: one named sorry at line79.
- PaperN8Closure.lean: two named sorries (lines46/59); central log warning only.
- P6APTActual.lean and C7C8ActualAttempt.lean: empty logs, no compile evidence.
- C7C8ActualAttempt/P6APTActual are not imported by PaperN8Closure.

PaperN8Closure imports only N8RouteClosure and C9QThetaValuesNamed.  It does NOT
import C9PaperClosure, P6HullActual, P6LActual, P6TensorActual, or P6BridgeActual.
Those Wave2 actual-link components remain separate and are not consumed by the
current paper assembly.

## 7. PaperN8Closure audit summary

File: tmp/sheaf/n8/closure/PaperN8Closure.lean
lines=137 bytes=5731 SHA256=c83e30af756593ae9ca6759dbc6dab22e64f95f60696b709173990af698b116f.
Two local named sorries: paperValuesBounded_obligation,
paperQLeTheta_obligation.  No total-goal sorry; no ABC/Cor312 import.

Findings:
- q/theta/values are not free fields: q_eq, theta_eq, values_eq tie them to
  route.chainA.Q, route.readout.ellOutValue and ValuesNamed.  No arbitrary Real
  field is introduced.
- The route field is N8RouteObligations.  Its chainB field is the Prop
  P6ChainB.MissingSLToCompleteAlpha, not an actual CompleteAlpha/R_alpha datum;
  its hull field is an abstract P6Hull.P6HullSetup filled by a named gap.  Thus
  "P6 source closure" in the PaperN8Closure docstring overstates the content; it
  is a P6 route-obligation package.
- The comparison field is P6Exact or P6Epsilon over SourceAllowedOutput X; it is
  an exact named gap and does not accept Q<=Theta.  Q<=Theta remains a concluded
  field, not an input.
- The paper file duplicates ValuesBounded/ValuesNamed even though
  C9PaperClosure already provides PaperC9Output, ValuesBounded,
  QInRleqTheta and paperC9Output_nonempty.  This is redundancy, not a free
  field, but it means the current assembly does not consume the Wave2 C9 paper
  component it was asked to reuse.

Exact correction suggestions (target not changed this round):
1. Import C9PaperClosure and replace local PaperValuesBounded/ValuesNamed with
   PaperC9Output.  Derive q/theta/values from PaperC9Output; use
   C9PaperClosure.ValuesBounded and QInRleqTheta as the exact C9 fields.
2. Rename/document route as P6 route obligations, or add an actual
   P6ChainB.CompleteAlpha/R_alpha field and an instantiated P6Hull setup instead
   of the abstract/named fields; do not call it source closure.
3. Remove duplicate PaperValuesBounded/paperValuesBounded_obligation after
   switching to C9PaperClosure; keep the single C9 ValuesBounded named gap.
4. Keep PaperN8Output.q/theta/values derived from components rather than stored
   fields; if stored, keep the equality constraints.
5. PaperComparisonJRange is descriptive and unused; keep only in audit text, not
   as evidence.

Legacy exclusion: N8FullOutput, N8Closure.lean old C0 assembly, N8ClosureAchieved
legacy named assembly and the old C10 closure are NOT part of this paper route
and are not imported by PaperN8Closure.

## 8. Wave3 status

Current paper route remains a named-sorry closure.  Wave1/2 central logs show no
error lines for the listed files but do not establish kernel closure.  The exact
residuals are the PaperN8Closure local two gaps, the imported P6 route gaps, and
the C9 source-existence gaps listed in PaperClosureStatus.md.  No paper N8
closure is claimed.
