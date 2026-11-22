# Paper closure status (current N8 paper route)

Updated: 2026-10-24.  Scope: current paper N8 route only (N8RouteClosure,
C9PaperClosure, C9QThetaValuesNamed, P6 components, PaperN8Closure).  ABC/Cor312
and the old Layer0/Layer1 closures are excluded.  Compilation of docs is not
applicable; Wave1/2 compile status is the central-log evidence recorded here.

Legacy exclusion: N8FullOutput, old N8Closure.lean C0 assembly,
N8ClosureAchieved legacy named assembly and the old C10 closure are NOT part of
this route and must not be reported as paper N8 closure.

## 1. Wave1/Wave2 centrally compiled components

Central logs were read from tmp/sheaf/n8/closure/wave1-*.log and
wave2-*.log.  A log with warnings only is listed as "warnings"; an empty log
means no diagnostics were recorded, not kernel closure.  Exit codes are not
stored in these logs.

| component | central log | named sorry evidence | imported by PaperN8Closure |
|---|---|---|---|
| C3T11NamedClosure.lean | wave1, warning line77 | 1 | no |
| C6C7C8NamedClosure.lean | wave1, empty | none recorded | no |
| C9P6Closure.lean | wave1, warning line121 | 1 | no |
| C9QThetaValuesNamed.lean | wave1, warnings lines87/93/99 | 3 | yes (direct) |
| N8RouteClosure.lean | wave1, warnings lines50/57 | 2 local + imported P6 gaps | yes (direct) |
| P6Bridge.lean | wave1, warning line70 | 1 | no |
| P6LClosure.lean | wave1, warning line51 | 1 | no |
| P6SHEIndClosure.lean | wave1, empty | none recorded | no |
| C9PaperClosure.lean | wave2, warning line140 | 1 | no (audit finding) |
| P6BridgeActual.lean | wave2, warning line70 | 1 | no |
| P6HullActual.lean | wave2, warning line84 | 1 | no |
| P6LActual.lean | wave2, warning line61 | 1 | no |
| P6TensorActual.lean | wave2, warning line79 | 1 | no |
| P6APTActual.lean | wave2, empty | none recorded | no |
| C7C8ActualAttempt.lean | wave2, empty | none recorded | no |
| PaperN8Closure.lean | wave2, warnings lines46/59 | 2 | this target |

The current PaperN8Closure imports only N8RouteClosure and
C9QThetaValuesNamed.  It does not import C9PaperClosure or the *Actual Wave2
components (P6HullActual/P6LActual/P6TensorActual/P6BridgeActual), so those
compiled components are available but not consumed by the paper assembly.

## 2. Current component hashes

| file | lines | SHA256 | local named sorry |
|---|---:|---|---:|
| N8RouteClosure.lean | 103 | 248557df33529c3381c4fe2b19594bd39db5da87d5b03dfcfe7e18c597cdec1c | 2 |
| C9PaperClosure.lean | 150 | 3094125b1462769e1fd641f4bbdf3da8a3609d7e3e6f4c0a7be1c215e49a20bb | 1 |
| C9QThetaValuesNamed.lean | 103 | 90d48bbbbb07229072adb19133f7db9c6e882ab701779e2dd016e9d202adeac4 | 3 |
| P6ChainA.lean | 104 | 4dabd544b3f0b5b0d166b66cfda825557ad48f7756e23208b9f3e34fdd1adf6c | 1 |
| P6ChainB.lean | 91 | 95e607df6ddde443a20cac586c1c588d0a2b620923f5b1f878a18e4e9f9ee827 | 1 |
| P6Hull.lean | 110 | b9dce54894a9eada7fde40d779e1801e05d869bdd145c537f5eb4ee6f73b63c1 | 0 |
| P6L.lean | 107 | 03fe51320a72e44fb7094adea00eefb3fff011228ff1c183a0d774e767cb96f2 | 1 |
| P6Comparison.lean | 146 | 984249410dbc1d4bfdc9058b32d6162dea913cfd45316a39f5259cadb5011a28 | 1 |
| PaperN8Closure.lean | 137 | c83e30af756593ae9ca6759dbc6dab22e64f95f60696b709173990af698b116f | 2 |

## 3. PaperN8Closure contents

Imports: N8RouteClosure, C9QThetaValuesNamed.

Local declarations:
- PaperValuesBounded X mu R : Prop := forall z, z in ValuesNamed X mu -> z <= R.ellOutValue.
- paperValuesBounded_obligation : PaperValuesBounded X mu R := by sorry.
- paperQLeTheta_obligation (O : N8RouteObligations X mu) :
    O.chainA.Q <= O.readout.ellOutValue := by sorry.
- structure PaperN8Output X mu with route : N8RouteObligations X mu; q ; theta ;
  values ; q_eq ; theta_eq ; values_eq ; valuesBounded ; q_le_theta.
- PaperN8Output.q_eq_route (proved).
- PaperComparisonJRange X (descriptive set of J range).
- paperN8Closure_nonempty : Nonempty (PaperN8Output X mu), assembled from the
  named ValuesBounded/Q<=Theta gaps.

No ABC/Cor312 import.  No free q/theta/values: q_eq/theta_eq/values_eq tie them
to route chainA.Q, route readout ellOutValue and ValuesNamed.

## 4. Exact named gaps

Local to PaperN8Closure:
1. paperValuesBounded_obligation.
2. paperQLeTheta_obligation.

Imported through N8RouteClosure:
3. p6HullSetup_nonempty (abstract P6Hull.P6HullSetup).
4. p6ComparisonObligation (P6Exact or P6Epsilon over SourceAllowedOutput X).
5. P6ChainA.globalLqDonor_nonempty.
6. P6ChainB.missing_sl_to_complete_alpha.
7. P6L.p6ReadoutExists_obligation.
8. P6Comparison.sourceAllowedOutput_nonempty (available, not constructed).

Imported through C9QThetaValuesNamed:
9. missing_q_source.
10. missing_theta_source.
11. missing_values_source.

C9PaperClosure also has a separate named gap:
12. paperC9Output_nonempty (not imported by current PaperN8Closure).

## 5. Exact residual / audit findings

A. Source closure wording is too strong.  N8RouteObligations.chainB is the Prop
   P6ChainB.MissingSLToCompleteAlpha, not an actual CompleteAlpha/R_alpha datum;
   its hull is an abstract P6Hull.P6HullSetup filled by a named gap.  Therefore
   PaperN8Output.route is a P6 obligation package, not a constructed P6 source
   closure.

B. C9PaperClosure is not consumed.  PaperN8Closure duplicates
   PaperValuesBounded and ValuesNamed instead of using
   C9PaperClosure.PaperC9Output, ValuesBounded, QInRleqTheta and
   paperC9Output_nonempty.  This is redundancy, not a free field, but it does
   not satisfy the requested reuse of the Wave2 C9 paper component.

C. Free-field audit: q/theta/values are constrained by equalities, so they are
   not arbitrary values.  valuesBounded and q_le_theta are named obligations,
   not free construction data.  No unconstrained Real/Set field was found.
   The route/hull/chainB fields are abstract obstacles, not fake data, but they
   must not be reported as constructed source objects.

D. J independence: comparison ranges over P6Comparison.SourceAllowedOutput X;
   Q<=Theta is only a concluded PaperN8Output field, never an input to the P6
   comparison.  This part is correct.

Exact correction suggestions (Lean target not changed this round):
1. Import C9PaperClosure; set PaperN8Output.c9 : PaperC9Output X mu and derive
   q/theta/values from it; use C9PaperClosure.ValuesBounded and QInRleqTheta;
   remove duplicate PaperValuesBounded/paperValuesBounded_obligation.
2. Rename route as p6RouteObligations, or add actual
   P6ChainB.CompleteAlpha/R_alpha data and an instantiated P6Hull setup instead
   of the abstract missing fields; do not call it source closure until then.
3. Keep PaperN8Output.q/theta/values derived from component fields (or retain
   the equality constraints if stored).
4. Keep PaperComparisonJRange only as audit description, not evidence.
5. Keep legacy N8FullOutput/C10 named closure excluded.

## 6. Wave3 status

Current paper route is a named-sorry closure, not a constructed paper N8
closure.  Wave1/2 central logs show no error lines for the listed files, but no
kernel/axiom audit or project build was run in this round.  Exact residuals are
the named gaps in section 4 and the two audit corrections A/B.  No paper N8
closure is claimed.
