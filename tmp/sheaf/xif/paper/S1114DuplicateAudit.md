# S1114 — audit: S1070–S1093 vs older paper files

Date: 2026-10-30.  Scope: every Lean file S1070–S1093 in `tmp/sheaf/xif/paper/`.
Comparison set: `PaperXiFFinalActual`, `RootNormalizedContainmentActual`, `S824RootStackyHaarVolumeActual`,
`S885RootStackUniformizerNormActual`, `S901NormCompatibilityActual`, plus the actual predecessors
`S826CNormOrderRamificationActual`, `S827PaperValueGroupNormCardActual`,
`QVFamNormalizedCoefficientOrderAuditActual`, `S118QVFamNormRatioValueActual`,
`S1062QPilotClassicalHullActual`, `S1063PerBQPilotPaperNonzeroActual`, `S1065OldPathQPilotAuditActual`.

## Verdict summary

* Genuinely new (keep): root-stack carrier object, pushforward Haar construction, q[1u] coefficient positivity/log,
  S1087/S1088 containment chain, S1093 new-object assembly.
* Duplicated / superseded (stop or alias): S1070/S1072/S1077 region-log definitions; S1074/S1078 e=1 iff (S826);
  S1088/S1089 coefficient/residue formula (QVFamNormalizedCoefficientOrderAudit + S118);
  S1076 exact hull positivity (superseded by S1080/S1082/S1084/S1102); S1084/S1091 witness;
  S1093 finite-link evidence (S1044 generic).
* Changed target, not literal duplicate: `PaperXiFFinalActual` (old `ActualPaperXiFTarget`, c_norm model) and
  `RootNormalizedContainmentActual` (c_norm qPilot region/hull).  New S1070/S1072 use the default/pure coefficient.

## Per-file audit

| file | verdict | duplicate / relation |
|---|---|---|
| S1070CanonicalQPilotRegionActual | duplicate construction, new coefficient choice | `canonicalQPilotRegion` / `canonicalQPilotLog` repeat `RootNormalizedContainmentActual.qPilotNormRegion` / `qPilotNormLog_eq` and `RootHullContainmentInequalityActual.qPilotClassicalRegion`. Only `qVFamPureCoefficient` (default-norm coefficient) and the exact supply interface are new. |
| S1070S1063IntermediateAuditActual | audit only | restates S1063/S1065 conclusions; no new mathematical content. |
| S1072CanonicalQ1URegionActual | mostly duplicate | `qPilotQ1URegion` is the same definition as S1070 `canonicalQPilotRegion` (rfl); log formula repeats S1070 `canonicalQPilotLog_eq_of_supply`. New: `qVFamPureCoefficient_pos`, per-b log negativity. |
| S1073RootStackPaperThetaHullActual | genuinely new object | `rootStackEmbedding`, `rootStackPaperThetaHull` are new (root-stack extension), but they consume S793/S805 `paperLambdaORegion`, `paperRootCoefficientFamily`; `rootStackPaperThetaHaar` is S824 `rootStackHaar`. Different from old `paperRootThetaHullNonzero` (S805/S900), which S1065 shows equals `qPilotPaperRegion`. |
| S1074SupplyCNormOrderActual | duplicate exact content | `S1074SupplyCNormEqOrder`, `NormCompatibilityOne`, `S1074ExactMinimal` restate S826 `QVFamNormalizedNormCompatibility` / `qVFamNormalizedCoefficient_eq_order_div_e` and S827 card. No new proof. |
| S1076RootStackPaperThetaHullMeasureActual | superseded exact version | exact positivity/covering of transported hull; superseded by S1080 pushforward + S1081/S1082/S1084 domain actual + S1102 actual conditional. Keep only as history; do not cite as active positivity. |
| S1077CanonicalQPilotQ1uActual | duplicate alias | `qPilotQ1uRegion`/`qPilotQ1uLog` are aliases of S1070 `canonicalQPilotRegion`/`canonicalQPilotLog`; `qPilotQ1uLog_eq_of_supply` repeats S1070. |
| S1078CNormOrderIffActual | duplicate exact content | exactly S826 `qVFamNormalizedCoefficient_eq_order_iff_e_eq_one` and `..._ne_order_of_e_ne_one`; no new arithmetic. |
| S1079RootStackMeasureAuditActual | genuinely new audit | range/proper-range dichotomy and `s1079HaarOnRange`; new distinction from S824 ambient stacky Haar. |
| S1080PushforwardConstructionActual | genuinely new construction | `s1080PushforwardHaar` and `S1080EqS824StackyMeasure`, `S1080AmbientZeroOnRange`; distinguishes pushforward from S824 stacky Haar. |
| S1081LambdaODomainHaarActual | partly duplicate | `s1081LambdaO_eq_qPilotPaperRegion` is definitional (already implicit in S793/S805); domain finiteness actual is new packaging. |
| S1082LambdaOPositivityExactActual | duplicate reduction | reduces positivity to scaled-unit witness already in S1083/S1084; new only the exact S1082 wrapper. |
| S1083ScaledUnitWitnessActual | genuinely new witness interface | integer witness structure used by S1084; not in old files. |
| S1084IntegerWitnessActual | genuinely new actual witness | constructs N, generator, norm, bound, witness; proves domain positivity actual. |
| S1085PushforwardHullEqActual | genuinely new pushforward identity | map_image_of_injective + hull equality reduction; injectivity repeated in S1090/S1095. |
| S1086PerBQ1URootHullActual | genuinely new per-b result | q[1u] log <= root-stack theta hull log via containment + pushforward + monotonicity; new target vs S1063 (c_norm vs paperRootThetaHullNonzero). |
| S1087Q1UContainmentActual | genuinely new | coefficient comparison => q1u region containment in paper lambda-O region; not in old files. |
| S1088CoeffLeActual | duplicate formula + new bridge | `qVFamPureCoefficient_eq_default` and `qVFamDefaultCoefficient_eq_order_mul` repeat QVFamNormalizedCoefficientOrderAudit; new part is `S1087CoeffLe_actual`. |
| S1089RatioActual | duplicate arithmetic | residue norm base-p power and ratio >= 1 repeat S118/QVFamNormRatioValueActual; new only packaging for S1088. |
| S1090EmbeddingFactsActual | partial duplicate | injectivity repeats S1095 `rootStackEmbedding_injective_actual`; measurability/closedness reduction new packaging. |
| S1091QPilotQ1UPositivityActual | partly duplicate | `s1091N`, `s1091Generator`, `s1091Generator_norm`, `s1091Data`, `s1091Bound` duplicate S1084 `s1084N` etc.; only q1u-region positivity/finiteness is new. |
| S1093PaperAssemblyActual | new-object assembly, duplicated helpers | certificate/PaperXiFInput assembly with q1u + root-stack hull; helper `S1093IPLSHEAPTEvidence` / `s1093FiniteLinks` duplicate S1044 generic `finiteLinkEvidenceOfHullTarget`; old `PaperXiFFinalActual` is a different target and must not be cited as this assembly. |

## Old files: what they already contain

* `PaperXiFFinalActual.paperLevelXiF_actual` — old `ActualPaperXiFTarget` (c_norm model), NOT the canonical q[1u] / root-stack theta-hull target.  Legacy; does not supersede S1093 but must not be cited as the new paper target.
* `RootNormalizedContainmentActual` — c_norm qPilot region (`qPilotNormRegion`), c_norm/(2l) root hull, qPilot log/containment.  S1070/S1072 repeat this construction with `qVFamPureCoefficient`; the coefficients are different objects.
* `S824RootStackyHaarVolumeActual` — actual root-stack Haar, stacky unit-ball log volume, and the theorem `stackyLog_eq_paperLeastHullLog_iff_cnorm_eq_order` / `..._ne...`.  S1073/S1076 must reuse `rootStackHaar`; S1074/S1078 restate the same c_norm = order iff, so no new proof needed there.
* `S885RootStackUniformizerNormActual`, `S901NormCompatibilityActual` — exact uniformizer/norm-compatibility cards.  S1074/S1078 are wrappers of the same content; further `c_norm = order` files would be duplication.
* `S826CNormOrderRamificationActual` / `S827PaperValueGroupNormCardActual` — already give exact `c_norm = order/e`, iff e=1, and the value-group norm card.  S1074/S1078 duplicate them.
* `QVFamNormalizedCoefficientOrderAuditActual` / `S118QVFamNormRatioValueActual` — already give `qVFamDefaultCoefficient = order * (log residue/log p)`, the ratio, and residue degree.  S1088/S1089 duplicate them.
* `S1062/S1063/S1065` — old c_norm qPilot vs `paperRootThetaHullNonzero`; S1065 proves old hull collapses to `qPilotPaperRegion`.  The new root-stack hull is a genuinely different target, but the old per-b inequality S1063 is the template S1086 repeats for the new hull.

## Stop-duplication rules

1. Freeze S1070 as the single definition of `canonicalQPilotRegion`/`canonicalQPilotLog`; make S1072/S1077 aliases only, no new copies.
2. Use S1073 only for the root-stack object; use S824 `rootStackHaar` directly, do not redefine it.
3. Do not add S1076-style exact positivity; S1080+S1081/S1082/S1084+S1102 now give the actual conditional result.  Keep S1076 as history only.
4. Do not add new `c_norm = order` wrappers; cite S826/S827 (and S824 stacky iff) directly.  S1074/S1078/S885/S901 are already redundant.
5. Do not add new coefficient/residue formula files; cite QVFamNormalizedCoefficientOrderAudit and S118.  Keep only the S1087 bridge if needed.
6. Reuse S1084 integer witness in S1091; eliminate S1091's duplicate N/generator/norm/bound.
7. Reuse S1044/S1054 generic finite-link construction in S1093; eliminate `S1093IPLSHEAPTEvidence` duplication.
8. Mark `PaperXiFFinalActual` and `RootNormalizedContainmentActual` as legacy c_norm path; do not cite as canonical q[1u]/root-stack paper target.

## Current active chain (not duplicate)

`S1070/S1072 (q[1u] region/log) + S1084/S1091 (positivity/finiteness) + S1073/S1080/S1085/S1095 (root-stack hull/pushforward/measurability) + S1102 (hull pos/fin) + S1086/S1087/S1088 (per-b inequality/containment) + S1093 (PaperXiFInput/certificate/finite links) + S1103 (weighted global) + S1106 (theta_agrees) + S1107 (qParameter card)`.
