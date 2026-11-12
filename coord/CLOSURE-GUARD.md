# Closure guard: target classes are not interchangeable

Date 2026-10-24. Binding project rule.

## Rule

`legacy closure` and `old Layer0/Layer1 closure` MUST NOT be reported, linked, or consumed as `paper N8 closure`.

## Target classes

| class | file/evidence | status | may be called paper N8 closure? |
|---|---|---|---|
| legacy C10 target named-sorry closure | `tmp/sheaf/n8/closure/N8ClosureFull.lean` | provisional named-sorry closure | NO |
| old Layer0/Layer1/ABC closure | any old-layer file/node | off-route unless current N8 consumer needs donor | NO |
| paper N8 v3 / P6 target | C9-TARGET-V3 + P6 components | source objects open | only after target acceptance |

## Reporting rule

Every closure report must state:
1. target class (legacy / old-layer / paper-v3);
2. exact files/hashes;
3. named sorries and simplifications;
4. `target_accepted` value.

Omitting the target class is a reporting violation.

## Prohibitions

- Do not put legacy closure in the paper N8 dependency chain.
- Do not use old layer closure to discharge C0/C1/C4/C7/C9 paper obligations.
- Do not use `N8FullOutput` legacy target as comparator/target-accepted evidence for C9-TARGET-V3.
- Do not claim `N8 closed` without qualifier `legacy target named-sorry closure` or `paper target target_accepted`.

## C10 rule

C10 paper assembly may reuse a legacy lemma only as a donor if an explicit adapter/identification theorem connects it to the paper target. Otherwise it stays a named gap.

## Active target decision (2026-10-24)

User does not want legacy closure. Active target is paper N8: C9-TARGET-V3/P6. Legacy `N8ClosureFull` is archived scaffold only; it is not active N8 closure and must not be used as target evidence.

## 2026-10-24 eta route guard

- Direct Q-scalar vs hull/readout comparison and trivialized-R/common-R arguments are CRITICIZED paths; do not use them as source closure.
- Frozen/relaxed direct-readout paper closures are archived as negative controls only.
- Active route: eta^q vs eta^anab_S via log-shell/integral structure, comparison before degrees. See IUT-ROUTE-ETA.md.

## 2026-10-24 C9 local-global counterexample guard

- Local linear isomorphisms/collection data do not imply a global linear morphism. Exact obstruction h-Q=S-kappa (kappa=deg A, S=deg Z>=0); example F=Q,p=3 L=3Z3,H=9Z3 has kappa=log3 and no global linear f.
- Therefore NO local-to-global Q<=Theta closure may be reported from local comparisons/collection existence alone. Global consumer must prove kappa=0 (realified principal divisor) or S>=kappa (source region enlargement), with actual A,Z.
- Local actuals (qO Haar/readout, shell action, tensor edges) are necessary, not sufficient.

## 2026-10-24 C9 consumer audit (binding)

Audit file: tmp/sheaf/n8/closure/C9-COUNTEREXAMPLE-AUDIT.md.

### Current consumer status

| consumer | current route | local-to-global? | required guard |
|---|---|---|---|
| PaperQLeThetaReduction.paperQLeTheta_of_comparison_valuesBounded / paperQLeTheta | P6Exact or P6Epsilon + ValuesBounded + P6EllOutInValues | NO (P6 global source gap) | if P6 gap is filled locally: d=1 and (kappa=0 or S>=kappa); epsilon: S>=kappa-epsilon |
| PaperC9ComparisonAttempt / N8RouteClosure.p6ComparisonObligation | named P6Exact/P6Epsilon obligation | NO | same P6 guard |
| P6Comparison.sourceAllowedOutput_nonempty | existence of source-allowed J only | NO | existence alone is NOT a Q<=Theta bound; no consumer may use it as one |
| P6EllOutBridgeAttempt.missing_p6EllOutBridge | per-J P6Readout carrier | NO | do not fill from local comparisons without global descent guard |
| PaperValuesBoundedReduction.p6LReadoutBound_obligation | global pointwise readout bound | NO | if derived per local comparison: actual A,Z,d and kappa=0 or S>=kappa |
| PaperN8Closure / PaperC10Closure / C10PaperFinalAssembly | inherit PaperQLeTheta | NO | inherit P6 guard |
| PaperN8RelaxedActual.relaxedPaperQLeTheta | direct named global gap | NO | if filled locally: P6 guard with actual degree data |
| SourcePilotApproximation.sourcePilotApproximation_stage2 | global source theorem named sorry | NO | if proved locally: P6 guard; q_le_theta_of_sourcePilotApproximation itself is a valid pure epsilon argument |
| EtaComparisonConsumer / Nondegenerate / Independent / V2 | paperQLeTheta | NO | inherit P6 guard; audit nondegeneracy guards do not replace kappa/S |
| EtaVaryingCalibrationActual.etaVarying_Q_le_Theta_of_sourceReadoutGaps | two global readout equalities | NO | if calibrated locally: P6 guard |
| C013Existence.n8_targetOutput_nonempty_sketch | intended source hull q_le_theta | NO | apply P6 guard before use |
| EtaLocalGlobalObstructionActual | LocalComparison identity and counterexample | NO global Q<=Theta | positive arithmetic model; keep A,Z actual, no free kappa/S field |

### Binding guards for any future global Q<=Theta discharge

- G1: d=1 (linear) or divide by Frobenius degree. d>1 gives h>=dQ, not Q<=h.
- G2 exact: actual A,Z with kappa=0 (realified principal divisor / global realified linear morphism) or S>=kappa (actual source region enlargement). Equivalently h-Q=S-kappa.
- G3 epsilon: S>=kappa-epsilon. No limit of local comparisons without uniform control on kappa-S.
- G4: A,Z,d from actual source local comparisons/gluing/Ob3 reference/common tensor normalization; no free kappa/S field, no target-defined A/Z, no independent local frame change.
- G5: collection existence, local linear isomorphisms, abstract pilot naturality, local Kummer layers are necessary but insufficient; use only after G2/G3.
- G6: no inverse through the negative-cut quotient; positive scaling f_a(t)=a t descends only for a>=1.
- G7: nonzero actual calibration class F(d)=d is an alternative sufficient anchor only when constructed; it does not replace G2/G3.

### Reporting rule

A closure/consumer report that concludes global Q<=Theta from local comparisons, local linear isomorphisms, or collection existence, without G2 or G3, is a target-class violation and must not be reported as paper N8 closure. target_accepted remains false until the global source comparison is constructed.

## 2026-10-24 hull volume endpoint guard

- arithmeticTupleHullUnitLogVolume is DONOR only (tensor block, unit-relative/nonneg), not P6 ellOut/Theta. Q<=h with h this volume does NOT imply Q<=Theta/ellOut. Do not set Theta:=h. Need actual hull=ellOut alignment on C6IQCarrier or actual kappa/S guard.
