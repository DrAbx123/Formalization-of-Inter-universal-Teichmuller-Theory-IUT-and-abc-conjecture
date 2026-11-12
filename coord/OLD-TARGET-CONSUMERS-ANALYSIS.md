# OLD-TARGET CONSUMERS ANALYSIS (mainline, A282)

Purpose: prevent reuse of the invalid pre-restatement path (A277). Deprecated symbols -> consumers -> needed change.

## 1. Mzk1Lemma24Goal (def: Mzk1Lemma24AssemblyActual:20; degenerate: iff beta notin S)
Consumers: Mzk1Lemma24AssemblyActual (assembly + base/step/transport); Mzk1Lemma24NormalizationTransferVariantActual (optional backup);
Mzk1Lemma24StepProvider2Actual/StepProvider3Actual (status mentions); audits S3232/S3243/S3244/S3178.
Needed: retire Goal; replace with restated 2.4 target (abc RestatedLemma24InterfaceActual: q Q[X], Sphi finite, q(S) subset Sphi, q(beta) notin Sphi, CV_C(q) subset {0,1,inf});
assembly/StepProvider files become historical or rewritten against restated target.

## 2. Mzk1Lemma24StepProviderStatement / Mzk1Lemma24BaseProviderStatement (defs: AssemblyActual:60/67)
Consumers: AssemblyActual (assembly + ledger), StepProvider2/3 status notes, S3232/S3236 audits.
Needed: replace with restated provider statements feeding restated 2.4; BaseProvider proof s3135_base_provider_complex targets old Goal - re-verify against restated; do not cite old provider statements.

## 3. Mzk1Lemma24Shape (def: Mzk1Thm25WiringActual; legacy shape)
Consumers: Mzk1Thm25WiringActual (h24 field + record), Hull11H6Mzk1UpgradeActual (h24 hypothesis), probes, ShapeStep/StatementShape files, old gate tables.
Needed: Thm25 wiring must CONSUME restated h22/h24 in conclusion (stepxi); restate Lemma24Shape over new target; Hull11/Hull-upgrade to be re-pointed or marked historical.

## 4. mzk1Lemma22_partial_induction (def: Mzk1Lemma22InductionActual:61; unconditional base/stepExists + lossy)
Consumers: Mzk1Lemma22InductionActual; Mzk1Thm25WiringActual (import/doc); Mzk1GChoiceDataOfHypothesesActual (doc: stepExists shape); Mzk1Lemma22FullGateActual; probes/audits; old gate tables.
Needed: rewrite induction interface to carry phi=gPoly + H-on-image + explicit C-point target; update consumers; remove old usage.

## 5. Mzk1Lemma22CompositionActual.comp (def: Mzk1Lemma22CompositionActual:29; ratFunc is PRODUCT bug)
Consumers (14 importers): GChoiceDataOfHypotheses, FullGateActual, GChoiceDataActual, InductionActual, StatementShapeActual, StepConstructionActual, PolyChainRule, PolyMap, PolyUnramifiedComposition, RationalDescent, GChoiceUnramifiedCanonical, StepProvider/NormalizationTransfer chain, audits/probes.
Needed: FIX def comp.ratFunc := psi.ratFunc.comp phi.ratFunc (true composition); then RE-COMPILE/RECHECK ALL 14 importers (risk: proofs relying on product may fail).

## 6. Mzk1Lemma22PartialShape (legacy partial shape)
Consumers: InductionActual, StatementShapeActual, Thm25WiringActual, EtTh09Status, old gate tables, audits.
Needed: restated target replaces PartialShape in consumer positions; legacy file stays historical only.

## 7. Thm25 wiring store-only defect (Mzk1Thm25WiringActual:129)
Needed (stepxi): conclusion must use h22/h24 (restated) + real consumer P1 composite 2.4 o 2.3 o 2.2 (2.3 Moebius); no store-only.

## 8. Other prerequisites
- CritIn01 over C (belyi21_derivative_root available) for paper-strength Lemma 2.1(b) / restated targets.
- Vocabulary unify P1Point Q + CV Set (P1Point C); specialSet={0,1,inf}; composition law + psi(specialSet) subset specialSet.

## 9. Restated files appearing (monitor)
- abc: RestatedLemma24InterfaceActual (created; status pending).
- shehdd: S3247CorrectedTargetChecklistActual (checklist).
- stage4: RestatedLemma22TargetActual (pending); comp/induction bugfixes (pending).
- stepxi: wiring consumer fix (pending).
- hull: CV/C-point helper (pending).

RULE: any import/use of symbols 1-6 must be re-pointed to restated interfaces or explicitly marked historical; no gate/closure claim under old target.