# S1094: audit of S1086/S1088/S1089/S1090/S1091

Date: 2026-10-30. Audit report.

## Existence / EXIT

* S1086PerBQ1URootHullActual.lean: exists, but local compile EXIT=1.
  Errors:
  - line 58: Unknown identifier s1079HaarOnRange;
  - line 88: hcont : S1086Q1UImageContainment T b does not match
    Set.image_mono's expected
    qPilotQ1URegion T b subset paperLambdaORegion cRoot.
* S1088CoeffLeActual.lean: exists, EXIT=0 (olean exists).
* S1089, S1090, S1091: absent from the tree (no files, no references).

## Axioms

S1088.s1087CoeffLe_actual:
  [propext, Classical.choice, Quot.sound]
S1088.qVFamPureCoefficient_ge_order:
  [propext, Classical.choice, Quot.sound]
Exactly the allowed trio.

S1086 cannot be axiom-audited because it does not compile.

## Correct q[1u]/root-stack content

S1087/S1088:
* qPilotQ1URegion is the canonical q[1u] region;
* rootStackPaperThetaHull uses paperRootCoefficientFamily = order/(2l);
* S1087CoeffLe is paperRootCoefficient <= qVFamPureCoefficient;
* S1088 proves S1087CoeffLe under S1088RatioGeOne
  (1 <= log(residueNorm)/log p), via
  qVFamPureCoefficient = order * (log residue/log p) >= order >= order/(2l).
This is the correct coefficient direction for q[1u] region subset root-stack
theta hull, but the S1086 measure/geometric assembly is not compiled.

S1086 intended statement is qPilotQ1ULogHaar <= rootStackPaperThetaHullLog,
using rootStackEmbedding, pushforward Haar, containment, measurability and
Haar equality.  Its exact inputs are S1086Q1UImageContainment,
S1085EmbeddingInjective/Measurable, S1086Q1URegionMeasurable,
S1086HaarEq, q[1u] positivity/finiteness, root-stack hull finiteness.

## Remaining exact

* S1086 compile fix: s1079HaarOnRange name/definition and hcont type mismatch.
* S1088RatioGeOne (residue degree condition) for S1087CoeffLe.
* S1087CoeffLe (conditional actual).
* S1086 geometric/measure inputs listed above.
* S1089/S1090/S1091 are missing exact files.

## Fake scan

grep sorry | axiom | True | PUnit | unsafe | admit:
S1086: 0, S1088: 0, S1087: 0.

No fake; no paper claim from the intermediate/missing chain.
