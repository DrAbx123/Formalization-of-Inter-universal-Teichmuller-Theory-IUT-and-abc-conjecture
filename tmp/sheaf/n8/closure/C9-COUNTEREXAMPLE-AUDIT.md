# C9 counterexample audit: local comparisons vs global Q <= Theta

Date: 2026-10-24
Auditor: transport
Source: C9-LOCAL-GLOBAL-DESCENT-ATTACK-20261024.md; C9-CONTRADICTION-ATTACK-20261024.md;
EtaLocalGlobalObstructionActual.lean.
No Lean files changed. CLOSURE-GUARD updated separately.

## 1. Obstruction being audited

For a fixed normalized global arithmetic model, a local comparison of Frobenius
degree d with local multiplier divisor A and effective zero divisor Z satisfies

  d * alpha + Z = beta + A,    Z >= 0,

and after weighted degree:

  h - d*Q = S - kappa,    S = deg Z >= 0,  kappa = deg A.

For d = 1:

  h - Q = S - kappa.

A global realified linear morphism exists only if kappa = 0 (A is a realified
principal divisor). If h < Q then necessarily

  kappa = Q - h + S > 0.

The two-place counterexample (Q, p=3): alpha=(-1,0), beta=(-2,0), A=(1,0),
Z=(0,0) has Q=-1, h=-2, kappa=1, S=0, local linear isomorphisms at all places,
and no global linear effective morphism. A degree-2 global morphism exists
because beta=2*alpha; it only proves 2Q<=h, not Q<=h.

Consequences:
- local linear comparison or collection-object existence does NOT imply
  global h >= Q;
- the exact sufficient guards are kappa=0, or S>=kappa (actual source region
  enlargement), with actual A, Z, d from real source arrows;
- for epsilon-cover: S >= kappa - epsilon gives h >= Q - epsilon;
- d>1 must be divided out or normalized; it does not give Q<=h.

## 2. Current closure / consumer inventory

Legend:
- GLOBAL = the named proposition is a global source statement, not inferred from
  local comparisons by the current file.
- LOCAL-IF = the file does not infer it locally, but a future discharge from
  local comparisons would need the guard.

| consumer | current route | local->global? | guard needed now / if filled |
|---|---|---|---|
| PaperQLeThetaReduction.paperQLeTheta_of_comparison_valuesBounded | P6Exact or P6Epsilon + ValuesBounded + P6EllOutInValues | NO; P6 comparison is GLOBAL | if P6 comparison is filled from local comparisons: d=1 and (kappa=0 or S>=kappa); epsilon: S>=kappa-epsilon |
| PaperQLeThetaReduction.paperQLeTheta | same via missing_p6EllOutInValues + paperC9Comparison | NO; both named global gaps | same guard on P6 comparison and ellOut-in-Values bridge |
| PaperQLeThetaReduction.missing_p6EllOutInValues | P6EllOutBridgeAttempt.p6EllOutInValues_via_bridge | NO; per-J carrier bridge is GLOBAL | if bridge built from local comparisons: actual global descent guard |
| P6EllOutBridgeAttempt.missing_p6EllOutBridge | every J has a P6Readout with matching ellOut | NO; named carrier gap | collection existence alone is insufficient; require global comparison guard |
| PaperC9ComparisonAttempt.paperC9Comparison_of_route | N8RouteClosure.p6ComparisonObligation | NO; named global source obligation | same P6 guard |
| N8RouteClosure.p6ComparisonObligation | P6Exact / P6Epsilon | NO; named global | same P6 guard |
| P6Comparison.sourceAllowedOutput_nonempty | existence of source-allowed J | NO; existence only | NOT a Q<=Theta source; existence alone gives no bound |
| PaperValuesBoundedReduction.p6LReadoutBound_obligation | forall P6Readout, value <= Theta | NO; global pointwise bound | if built from local comparisons: need global descent or actual S>=kappa per readout |
| PaperN8Closure.paperQLeTheta / paperQ_le_theta | PaperQLeThetaReduction + ValuesBounded | NO; inherits global gaps | inherits P6 guard |
| PaperC10Closure / PaperC10FinalAssembly | PaperN8Closure route | NO; inherits | inherits P6 guard |
| PaperN8RelaxedActual.relaxedPaperQLeTheta | direct named Prop R.Q <= G.value | NO; direct global gap | if filled from local comparisons: P6 guard with actual degree data |
| C9.sourcePilotApproximation_stage2 | actual_values_bounded + actual_q_approximated | NO; source theorem named sorry | final epsilon implication is valid, but filling the source theorem by local data needs P6 guard |
| C9.q_le_theta_of_sourcePilotApproximation | epsilon argument | NO; pure Real argument | no additional guard for the implication itself |
| EtaComparisonConsumer.etaNormalizedQ_le_Theta | paperQLeTheta | NO; inherits | inherits P6 guard |
| EtaComparisonConsumerNondegenerate | paperQLeTheta + audit guards | NO; audit guards are nondegeneracy only | inherits P6 guard; nondegeneracy guards do not replace kappa/S |
| EtaConsumerIndependent | paperQLeTheta | NO; inherits | inherits |
| EtaConsumerV2 | paperQLeTheta + D.valuesBounded | NO; inherits | inherits |
| EtaVaryingCalibrationActual.etaVarying_Q_le_Theta_of_sourceReadoutGaps | two global readout equalities | NO; calibration equalities are global | if calibrated by local comparisons: P6 guard; varying-region readout equality is not a local degree computation |
| C013Existence.n8_targetOutput_nonempty_sketch | intended source hull q_le_theta | NO; draft named sorry | if filled from local comparisons: P6 guard |
| EtaLocalGlobalObstructionActual | LocalComparison degree identity and counterexample | NO global Q<=Theta attempted | positive model: kappa/S identity; not a consumer |

## 3. Verdict

No current closure/consumer in the audited set derives global Q<=Theta from
local comparisons or from collection-object existence.  The current global
Q<=Theta routes are either:

- explicit named global source gaps: P6Comparison/P6Exact/P6Epsilon,
  P6EllOutInValues, P6LReadoutBound, relaxedPaperQLeTheta,
  sourcePilotApproximation_stage2;
- or pure Real implications from an already-global comparison
  (PaperQLeThetaReduction, q_le_theta_of_sourcePilotApproximation).

So the counterexample does not currently break a Lean theorem.  It breaks the
candidate future discharge: filling any of the GLOBAL gaps above from local
comparisons/collection existence, without kappa=0 or S>=kappa, is invalid.

The named global gaps must therefore carry an explicit guard record when they
are eventually filled.  A closure report that says local comparisons exist
or the local-global collection is nonempty and then concludes Q<=Theta is a
reporting violation.

## 4. Required guards

G1. Degree normalization.  Use d=1 (linear) or divide by the Frobenius degree
    before comparing Q and h.  d>1 alone gives h>=dQ, not Q<=h.

G2. Exact global descent.  For each actual local comparison supply actual
    A, Z and prove either
      kappa = 0 (A is a realified principal divisor; global realified linear
      morphism), or
      S >= kappa (actual source region enlargement / effective zero surplus).
    Equivalently h>=Q by h-Q=S-kappa.

G3. Epsilon global descent.  For an epsilon-cover prove S >= kappa - epsilon
    (then h >= Q - epsilon).  Do not replace this by a limit of local
    comparisons without a uniform control on kappa-S.

G4. Actual data, not free fields.  A, Z, d must come from the real source
    local comparisons/gluing/Ob3 reference and common tensor normalization.
    No independent local frame change, no free kappa/S field, no target-defined
    A/Z.  The EtaLocalGlobalObstructionActual.LocalComparison identity and
    counterexample are the reference model.

G5. Collection existence is not a bound.  Nonempty local-global collection,
    local linear isomorphisms, BPS abstract pilot naturality and local Kummer
    layers are necessary but insufficient.  They may be used only after G2/G3.

G6. No inverse through the negative-cut quotient.  The positive scaling
    f_a(t)=a t induces a self-map of the cut quotient only for a>=1; inverse
    maps do not descend.  Do not use inverse loops to move a fixed q below a
    bad bound.  This is an additional guard on any cut-based attack, not a
    substitute for G2/G3.

G7. Alternative anchor guard.  A nonzero actual calibration class d with
    F(d)=d forces a=1.  It is an alternative sufficient route only when the
    nonzero class and its preservation are actually constructed; it does not
    replace G2/G3 in the current closure.

## 5. Per-file action list

1. PaperQLeThetaReduction.lean: keep the current conditional proof; annotate
   missing_p6EllOutInValues and paperC9Comparison with the G2/G3 guard
   requirement for any future donor.
2. P6Comparison.lean / N8RouteClosure.lean: p6ComparisonObligation and
   sourceAllowedOutput_nonempty must not be used as a Q-bound donor without
   the P6 guard record.  Existence of J is not a bound.
3. P6EllOutBridgeAttempt.lean: P6EllOutBridge is a carrier map; do not fill
   it from local comparisons without G2/G3.
4. PaperValuesBoundedReduction.lean: p6LReadoutBound_obligation is a global
   bound; if derived per local comparison, attach actual A,Z,d and G2/G3.
5. PaperN8Closure.lean, PaperC10Closure.lean,
   C10PaperFinalAssembly.lean: inherit the guards; no local shortcut.
6. PaperN8RelaxedActual.lean: relaxedPaperQLeTheta is a global named gap;
   do not fill it from local object existence.
7. SourcePilotApproximation.lean: q_le_theta_of_sourcePilotApproximation
   is valid as a pure epsilon argument; sourcePilotApproximation_stage2 is
   the global source gap needing G2/G3 if proved locally.
8. Eta consumers (ComparisonConsumer, Nondegenerate, Independent, V2,
   VaryingCalibrationActual): inherit G2/G3; nondegeneracy guards do not
   replace them.
9. C013Existence.lean: intended q_le_theta donor is a global source
   comparison; apply G2/G3 before use.
10. EtaLocalGlobalObstructionActual.lean: retain as the positive arithmetic
    model; do not turn MissingActualComparisonTargetData into a free field.

## 6. Status

- Current Lean global Q<=Theta consumers: no local-to-global inference found.
- Current named global gaps: still open; target_accepted=false.
- Counterexample effect: invalidates local-comparison/collection-existence
  discharge of those gaps without kappa=0 or S>=kappa.
- CLOSURE-GUARD updated with this audit.
