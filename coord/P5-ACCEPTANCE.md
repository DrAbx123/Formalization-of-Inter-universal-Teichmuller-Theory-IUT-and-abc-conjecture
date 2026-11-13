# P5 ACCEPTANCE — conditional analytic/root comparison

Date: 2026-11-13.  All P5 files are conditional; no analytic bridge is claimed.

## Green theorem chain

| File | Theorem/def | Status |
|---|---|---|
| Mzk1P5LabelShiftActual | thetaLabelExponent, analyticThetaLabelPoint, oddThetaFraction_eval_thetaLabel | GREEN |
| Mzk1P5QNormalizationInputActual | P5QNormalizationInput, p5_bridge_compare_of_qNormalizationInput | GREEN 22:37:38 |
| Mzk1P5PhaseRelationActual | P5PhaseRelationData, p5_phase_relation, p5_phase_pow | GREEN 22:40:17 |
| Mzk1P5CJConditionActual | p5_c_eq_one_iff (field version) | GREEN 22:46:19 |
| Mzk1P5PhaseDerivedActual | root_image_zpow, phase_relation | GREEN 23:04:16 |
| Mzk1P5CJDerivedActual | c_eq_one_iff theorem derived from phase_relation | GREEN 23:12:21 |
| Mzk1P5RootChoiceOrderActual | root_pow_l_square, root_pow_one_order | GREEN 23:09:25 |
| Mzk1P5HunitDerivedActual | actualP5Bridge_hunit (no hunit hypothesis) | GREEN 23:26:10 |
| Mzk1P5ComparisonDerivedActual | paperRootThetaUnit_eq_qRoot_zpow, toRoot_zpow, cOfPhase, comparison_cOfPhase | GREEN 23:40:59 |
| Mzk1P5PhaseExponentDataActual | PhaseExponentData | GREEN 23:47:58 |
| Mzk1P5FinalSummaryActual | P5NamedInputs, bridgeOfInputs, p5_final_comparison | GREEN 23:53:16 |

Primary final file: tmp/sheaf/xif/paper/Mzk1P5FinalSummaryActual.lean.
olean size 298960 B; p5_final_comparison axioms
[propext, Classical.choice, Quot.sound].

## Four remaining named inputs

P5NamedInputs (L R=l) has exactly:
1. toRoot : L ->+* RootExtension G v0;
2. r : L;
3. root_image : toRoot r = twoLthRootAt^l;
4. phase : PhaseExponentData l, i.e. m : ThetaLabel -> Nat.

c_j and hcomparison are NOT inputs: cOfPhase is
phase_j^(-1) * qRoot^(-((l+1)*n)), and comparison_cOfPhase proves
hcomparison.  p5_final_comparison gives the conditional comparison from the
four inputs.

## Why the analytic toRoot cannot be constructed here

RootExtension v = AlgebraicClosure (CommonPrimeCompletion (G.place v)).  It is
an algebraic closure: a Field, but with no NormedField/IsUltrametricDist/
CompleteSpace instance in the tree.  A P5 analytic field L must carry those
instances (oddTheta is a normed analytic construction).  Moreover the root
side is place-indexed, while a single toRoot must be one ring hom from the
analytic oddTheta field to one RootExtension v0.  No such global
place-compatible map (and no analytic theta/Kummer section) is present in
Mathlib or the project tree; constructing it requires the actual
analytic-to-algebraic place and Kummer-class identification, which is the
documented missing source.  Therefore toRoot/r/root_image remain named inputs.

External search: Iut/EtaleTheta/KummerClass.lean contains project-specific
Kummer theory (HasKummerRoots, kummer/kummerZHat, EtaleTheta Kummer classes),
but no Mathlib port of the analytic root map; it cannot supply toRoot.

## Internal-consistency check (NOT the analytic bridge)

tmp/sheaf/xif/paper/Mzk1P5InternalConsistencyActual.lean is GREEN
(DONE EXIT=0 2026-11-13T00:13:57.050Z, 56s; axioms [propext,
Classical.choice, Quot.sound]) as a *conditional packaging* theorem: given any
toRoot/r/root_image/phase it packages a P5NamedInputs (internalConsistency).
The stronger special case L=RootExtension, toRoot=id is NOT lawful: a
hypothetical NormedField instance on RootExtension introduces a Field instance
distinct from the canonical AlgebraicClosure.instField, a typeclass diamond in
RingHom.id.  No fake normed instance is added.  Thus this is a satisfiability
check of the four-field structure, not the analytic bridge; the actual
analytic bridge remains GAP.

## Axioms / discipline

All green P5 theorems report only [propext, Classical.choice, Quot.sound]
(root choice uses [propext, Quot.sound]).  No sorry/axiom in final sources;
no toy carrier substitution; no c_j=1 theorem; j=0 is excluded by ThetaLabel
(ROUTE3 8.14).  Earlier per-file logs contain failed attempts with temporary
sorryAx; final DONE blocks are decisive.

End of acceptance.
## Axiom audit log

File: tmp/sheaf/xif/paper/Mzk1P5AxiomAuditActual.lean (imports the green P5
chain, adds no theorem, #print axioms of the main theorems).

Observed audit output:
- p5_bridge_compare: [propext, Classical.choice, Quot.sound]
- p5_bridge_compare_of_qNormalizationInput: [propext, Classical.choice, Quot.sound]
- p5_phase_relation / p5_phase_pow: [propext, Classical.choice, Quot.sound]
- p5_c_eq_one_iff: [propext, Classical.choice, Quot.sound]
- root_image_zpow / phase_relation: [propext, Classical.choice, Quot.sound]
- c_eq_one_iff: [propext, Classical.choice, Quot.sound]
- root_pow_l_square / root_pow_one_order: [propext, Quot.sound]
- actualP5Bridge_hunit: [propext, Classical.choice, Quot.sound]
- paperRootThetaUnit_eq_qRoot_zpow / toRoot_zpow / comparison_cOfPhase:
  [propext, Classical.choice, Quot.sound]
- p5_final_comparison: [propext, Classical.choice, Quot.sound]

The first audit attempt reported p5_bridge_compare as unknown only because its
namespace was not opened; open was added, no theorem changed.  All printed
declarations contain no sorryAx and only allowed axioms.  Final watchdog DONE: 2026-11-13T00:25:03.516Z (65s); all #print axioms
outputs above are final and contain only the allowed axioms.

End of axiom audit.