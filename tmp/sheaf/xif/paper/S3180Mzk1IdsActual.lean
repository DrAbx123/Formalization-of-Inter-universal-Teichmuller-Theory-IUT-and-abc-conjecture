/-!
# S3180/Mzk1 ids (data only; pins 14041/23066/18800; no registry edits)

* INDEX.S3180.conditional-assembly (REBUILT post-honesty-audit v2) ->
  S3180ConditionalAssemblyActual: qPilotSignedReadout, thetaHullSignedReadout,
  qPilotSignedReadout_le_thetaHullSignedReadout, Cor312AssemblyInputs, toContract,
  cor312_conditional, abcConjecture_conditional, IUTMainTheoremShape,
  iutMainTheorem_conditional, cor312AssemblyFieldSources,
  documentationOnlyRemainingAssumptions, s3180TheoremDeps, s3180HonestyAuditFix.
  Signed readouts DEFINED from tree objects (S3131CanonicalRootedQC/HC); comparison
  DERIVED from unconditional S3131CanonicalRootedQC_le_HC; ipl/she/apt named
  content-free placeholders (NOT used); decorative fields removed -> documentation.
  CONDITIONAL ASSEMBLY, not closure.
* INDEX.MZK1.cor31-cor32-proof -> Mzk1Cor31Cor32ProofActual:
  finite_subcover_of_isCompact, cor31_finite_subcollection, isCompact_prod_set,
  cor32_finite_subcollection, Cor31ReductionData/cor31_reduction,
  Cor32ReductionData/cor32_reduction, mzk1CorProofWiring, mzk1CorProofStatus.
  A-class topological finite-subcover core proved; Mzk1 Thm 2.5 = class D paper-input
  (Mzk1Theorem25StatementActual placeholder not consumed); scheme-level Y/L_v/H_v
  geometry class B/D abstracted.
- checker: S3180 CITABLE 10 decls (EXIT0 174298; src 11109 07D3159D / olean 242288 13C034B1;
  probe _S3180Probe 174389); Mzk1 CITABLE 10 decls (EXIT0 173956; src 8521 B11FFF68 /
  olean 224120 F102F0E5; probe _Mzk1CorProofProbe 174147).
- Note: hull H2/H4/H7 reported CLOSED (Hull05 6845B CITABLE); upcoming
  S3182Cor312HullDetAssemblyActual will be consumable for the hull/det part; S3180's
  current tree comparison source is S3131CanonicalRootedQC_le_HC (unconditional).
**Component, not paper object.**  No sorry/axiom/True/PUnit/toy carrier (data file).
-/

namespace LeanFormal.IUT.XiFPaper.S3180Mzk1IdsActual

/-- S3180/Mzk1 ids: (index id, declarations, file). -/
def s3180Mzk1Ids : List (String × String × String) :=
  [ ("INDEX.S3180.hull-det-consumer",
      "conditionalAssembly_with_hullDet (consumes S3182Cor312HullDetAssemblyActual HullDetAssemblyInputs -> Cor312HullDetConclusion; q!=1 tree readouts; heightUndilated/regionUndilated)",
      "S3180ConditionalAssemblyActual.lean"),
    ("INDEX.AG.canonical-divisor-genus",
      "ag10CanonicalDivisor, ag10CanonicalDivisor_apply, ag10CanonicalClass, ag10Genus, ag10_ell_canonicalDivisor_eq_genus, ag10_degree_canonicalDivisor_eq, ag10Reuse",
      "AG10CanonicalDivisorGenusActual.lean"),
    ("INDEX.GEOMCORE.input-wiring",
      "geomCoreInputWiring, geomCoreWrapperPolicy",
      "GeomCore02WiringActual.lean"),
    ("INDEX.AG.proved-theorems",
      "ag14_serde_pairing_bijective, ag14_weilDualityAdelic_of_isAlgClosed, ag14_cechRiemannRoch_of_genusReached, ag14Reuse",
      "AG14ProvedTheoremsConsumerActual.lean"),
    ("INDEX.AG.finite-map-canonical",
      "ag15Reuse, ag15GeomCorePointers",
      "AG15FiniteMapCanonicalActual.lean"),
    ("INDEX.MZK1.belyi-canonical",
      "belyi_eval_zero, belyi_eval_one, belyi_natDegree_pos, belyi_card_collapse, belyi_criticalValues_subset, belyi_exists_polynomial_aeval, belyi_exists_polynomial_eval, belyi_rho_unit, mzk1BelyiRows, mzk1BelyiPortRefs",
      "Mzk1BelyiCanonicalActual.lean"),
    ("INDEX.AG.cech-riemann-roch",
      "ag12_cechRiemannRoch, ag12Reuse",
      "AG12CechRiemannRochActual.lean"),
    ("INDEX.AG.weil-duality-adelic",
      "ag13_weilDualityAdelic, ag13Reuse",
      "AG13WeilDualityAdelicActual.lean"),
    ("INDEX.MZK1.gchoice-critical-in-target",
      "lam_ne_zero_critical, eval_mem_image_of_mem, gChoiceCriticalInTarget_proved, gChoice_unramifiedShape_proved, gChoiceData_complete",
      "Mzk1GChoiceCriticalInTargetActual.lean (EXIT0 190696 SIZE 6601, checker CITABLE 4, src 9991FCF8/olean 124080 A0FC8562)"),
    ("INDEX.MZK1.gchoice-avoid-canonical",
      "gChoiceScaleData_lam_ne_zero, gChoiceScaleData_realBeta_ge_two, gChoiceScaleData_belyi21R_realBeta_ge_two, gChoice_card_lt, GChoiceUnramifiedShape, gChoice_canonicalBelyi_criticalValues, gChoice_avoids, gChoiceData_of_avoids, mzk1GChoiceAvoidRows",
      "Mzk1GChoiceAvoidCanonicalActual.lean (EXIT0 189819 SIZE 10839, checker CITABLE 9, src 61649B85/olean 333248 2385073C)"),
    ("INDEX.MZK1.gchoice-unramified-canonical",
      "gPoly_ne_zero, gPoly_unramified_infty, GChoiceDataUnramifiedShape, canonicalBelyi_criticalPoints_row, canonicalBelyi_criticalValues_row, GChoiceCriticalInTarget, gChoice_unramified_of_criticalInTarget, mzk1GChoiceUnramifiedRows",
      "Mzk1GChoiceUnramifiedCanonicalActual.lean (EXIT0 189655 SIZE 6635, checker CITABLE 10, src 80ABCE3D/olean 118672 0A86F6D8)"),
    ("INDEX.MZK1.rational24-basecase-bridge",
      "baseCaseProvider_discharged, ProblemCResidual, paperScopeLemma24Statement_of_provedBaseCase, rational24_and_baseCase_proved, rational24Target_finite_beta_available, rational24BaseCaseBridgeRows",
      "Mzk1Rational24BaseCaseBridgeActual.lean (EXIT0 209751 SIZE 5119; checker CITABLE 7; src 743514F1/olean 77408 5572AEDD; probe 209790) — B3 finite-beta 2.4 wired to abc BaseCaseProvider; only StepProvider remains; NO closure; gate NOT PASSED"),
    ("INDEX.MZK1.rational24-bottom",
      "Rational24TargetFiniteBeta, rational24TargetFiniteBeta_proved, Mzk1Lemma24Target_finite_beta_bottom, BaseProviderRestatedFinite, baseProviderRestatedFinite_proved, mzk1Lemma24Target_of_betaAvoidingBelyiBaseCorrected, oldBaseProviderPremise_refuted, restatedBaseStatementFinite_bottom, restatedInductionConclusionFinite_bottom, rational24BottomRows",
      "Mzk1Rational24TargetBottomActual.lean (EXIT0 209152 SIZE 5781; checker CITABLE 11; src A4D82E80/olean 86512 43E90BB2; probe 209153) — rational 2.4 target finite beta UNCONDITIONAL from B1 fold/B2; corrected base provider; spec repair; F=Q scope; NO closure; gate NOT PASSED"),
    ("INDEX.MZK1.consumer24-unconditional",
      "FiniteBetaCorrectedBase, finiteBetaCorrectedBase_proved, H24BaseConcreteFinite, h24BaseConcrete_finite_proved, h24BaseConcrete_finite, p1CompositeConsumerInputs_unconditional24(_h24Base/_h24Base_proved), p1CompositeConsumerStatement_unconditional24, p1CompositeRealConsumerTarget_unconditional24, unconditional24AdapterRows",
      "Mzk1Consumer24AdapterUnconditionalActual.lean (EXIT0 208570 SIZE 10264; checker CITABLE 12; src 60DC8BC2/olean 193224 796DF075; probe 208583) — Problem A fold base unconditional for finite beta; named premise removed; infinity-beta spec repair; finite-beta/F=Q scope; NO closure; gate NOT PASSED"),
    ("INDEX.MZK1.consumer-deep-inputs",
      "ProblemDDeepInputs, ProblemEDeepInputs, P1CompositeConsumerInputsDeep, mkDeepInputs, P1CompositeConsumerStatementDeep, P1CompositeConsumerDeepStatement, p1CompositeConsumerStatementDeep_of_FQ, p1CompositeConsumerDeepStatement_of_FQ, baseStatement_of_FQ, p1ConsumerDeepInputRows",
      "Mzk1P1ConsumerDeepInputsActual.lean (EXIT0 207981 SIZE 8734; checker CITABLE 11; src 10CAC8F2/olean 304240 287AB9B5; probe 208137) — Problem D/E named inputs explicit; conditional statements from F=Q target; consumed/named split; NO closure; gate NOT PASSED"),
    ("INDEX.MZK1.consumer24-adapter-wiring",
      "wiredInputs_h24Base_eq, wiredInputs_cvLaw_eq, wiredInputs_h24Base_supplied, wiredStatement_holds, p1CompositeRealConsumerTarget_wired, consumerWiringRows",
      "Mzk1Thm25P1CompositeConsumerWiringActual.lean (EXIT0 207308 SIZE 5810; checker CITABLE 7; src C0F5D65B/olean 77984 EE63A469; probe 207319) — abc adapter consumed; h24Base+h24BaseConcrete from BetaAvoidingBelyiBaseInput; CV law PROVED; F=Q scope; NO closure; gate NOT PASSED"),
    ("INDEX.MZK1.p1-composite-real-consumer",
      "polyEvalP1_eq_polyMapPoints, old_specialSet_eq_restated, cpointCriticalValuesIn01_of_target, moebiusInversion_mapPoints_zero/infty/finite, moebiusInversion_involutive, p1CompositeRealConsumerTarget_rational, p1Composite_mapPoints_consumer_rational, p1CompositeConsumerRows",
      "Mzk1Thm25P1CompositeConsumerActual.lean (EXIT0 206567 SIZE 9619; checker CITABLE 12; src 6E3326CC/olean 242528 6A741D44; probe 206597) — F=Q scope REAL consumer; rational gate USED; 2.2 o 2.3 composition PROVED; full-Qbar reduction NAMED; NOT closure; binding HOLD"),
    ("INDEX.MZK1.scope-split",
      "restatedLemma22Scope, AlgebraicNestedInductionInput, polyEvalP1AC, P1CompositeConsumerInputs (h24Base + algebraicNestedInduction)",
      "RestatedLemma22InterfaceActual (EXIT0 201668 SIZE 8624, CITABLE 13, src 434544AD/olean 131384 69EBE2C4) + Mzk1Thm25P1CompositeConsumerDesignActual (EXIT0 201949 SIZE 10500, CITABLE 12, src C82269A6/olean 267192 88B00A76) — F=Q base-only; full P1(Qbar) reduction NAMED; no closure; gate NOT PASSED"),
    ("INDEX.MZK1.restated-lemma22-interface",
      "Mzk1Lemma22Target, Good, Mzk1Lemma22Target_iff_exists_Good, Mzk1Lemma22InductionStatement, target_of_induction, Mzk1Lemma22CVCompat, Mzk1Lemma22TargetImpliesFullShape, restatedLemma22Rows",
      "RestatedLemma22InterfaceActual.lean (EXIT0 199972 SIZE 6012, checker CITABLE 7, src FDA5B47D/olean 97712 1A4B8F1A) — SINGLE SOURCE for stage4 induction; gate NOT PASSED"),
    ("INDEX.MZK1.thm25-real-consumer-design",
      "specialSetC, CPointCriticalValuesIn01, MoebiusData, MoebiusData.mapPoints, P1CompositeRealConsumerTarget, P1CompositeConsumerInputs, P1CompositeConsumerStatement, mzk1P1CompositeDesignRows, hullInterfaceNeeds",
      "Mzk1Thm25P1CompositeConsumerDesignActual.lean (EXIT0 199501 SIZE 6767, checker CITABLE 10, src B53B8E00/olean 182616 11EA0193) — DESIGN/STATEMENT ONLY; binding HOLD; gate NOT PASSED"),
    ("INDEX.MZK1.thm25-consumer",
      "Lemma22FullShapeGate, thm25_of_full2_and_24, lemma22FullStatementShape_of_gate, mzk1Thm25ConsumerRows(+_length)",
      "Mzk1Thm25ConsumerActual.lean (EXIT0 185663 SIZE 4720, checker CITABLE 5, src A081A21F/olean 76784 BA722C49)"),
    ("INDEX.MZK1.thm25-wiring",
      "Lemma22Hypotheses, Lemma22FullStatementShape (paper-conditioned named hypothesis), Lemma24Shape, Thm25WiringRecord, thm25_wiring, thm25_of_22_24_and_geometricCore, mzk1Thm25WiringRows(+_length), mzk1Thm25WiringResidual(+_length)",
      "Mzk1Thm25WiringActual.lean (EXIT0 180195 SIZE 10247, checker CITABLE 10, src A29424E3/olean CECF837E)"),
    ("INDEX.MZK1.gchoice-scale",
      "Lemma22Hypotheses, scaleP, scaleS, ScaleOrdering, scale_memberships_basic, scale_memberships_full, scaleRatS, scaleRealS, scale_realHypotheses_exists, posRatS, posRatS_card, scaleOrdering, scale_orderings_exists, scaleOrdering_of_hypotheses, scale_orderings_exists_of_hypotheses, gChoiceScaleRows",
      "Mzk1GChoiceScaleActual.lean (EXIT0 186218 SIZE 24462, checker CITABLE 29, src E0C00A45/olean 659824 D6FD955A)"),
    ("INDEX.MZK1.step-construction",
      "card_image_lt_of_not_injOn, card_image_lt_of_collision, p1_zero_ne_one, lemma22Step_card_lt, lemma22StepOfData, lemma22StepOfPoly, lemma22Step_exists, lemma22StepExists_packaged, lemma22Step_compose, lemma22StepObligations, lemma22StepCorpusRefs",
      "Mzk1Lemma22StepConstructionActual.lean"),
    ("INDEX.INDET.h7-ob9-wiring",
      "H7Ob9IndetWiring, h7Ob9IndetWiring, h7Ob9_comparison_ind1_invariant, h7Ob9_comparison_ind2_invariant, h7Ob9_comparison_ind3_one_sided, h7Ob9ConsumerInterface",
      "Indet06H7Ob9WiringActual.lean"),
    ("INDEX.ETTH.status-record",
      "etTh09StatusRows, etTh09OpenGates, etTh09Ids",
      "EtTh09StatusActual.lean"),
    ("INDEX.GEOMCORE.gated-assembly",
      "GeomCorePaperInput, GeomCoreOutputStatement, GeomCoreAssemblyStatement, GeomCoreAssemblyStatement_iff, geometricCoreDataOfFunction, geometricCoreDataOfFunction_nonempty, geomCore_conditional, geomCoreCanonicalAssets, geomCoreAssemblyPlan, geomCoreRemainingDischarge",
      "GeomCore03AssemblyActual.lean"),
    ("INDEX.AG.serre-pairing",
      "ag11ResidueTheorem, ag11SerrePairing, ag11SerrePairing_apply_mk, ag11SerdeReuse",
      "AG11SerrePairingConsumerActual.lean"),
    ("INDEX.S3183.hull-det-consumption",
      "hullDetConsumptionRecord, hullDetAuditRefs",
      "S3183HullDetConsumptionRecordActual.lean"),
    ("INDEX.S3180.conditional-assembly",
      "qPilotSignedReadout, thetaHullSignedReadout, qPilotSignedReadout_le_thetaHullSignedReadout, Cor312AssemblyInputs, toContract, cor312_conditional, abcConjecture_conditional, IUTMainTheoremShape, iutMainTheorem_conditional, cor312AssemblyFieldSources, documentationOnlyRemainingAssumptions, s3180TheoremDeps, s3180HonestyAuditFix",
      "S3180ConditionalAssemblyActual.lean"),
    ("INDEX.MZK1.cor31-cor32-proof",
      "finite_subcover_of_isCompact, cor31_finite_subcollection, isCompact_prod_set, cor32_finite_subcollection, Cor31ReductionData, cor31_reduction, Cor32ReductionData, cor32_reduction, mzk1CorProofWiring, mzk1CorProofStatus",
      "Mzk1Cor31Cor32ProofActual.lean") ]

end LeanFormal.IUT.XiFPaper.S3180Mzk1IdsActual
