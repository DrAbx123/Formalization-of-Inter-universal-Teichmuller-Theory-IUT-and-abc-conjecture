import LeanFormal.IUT.Audit.Status

/-! # S3131: project final residual registry (acceptance checklist; 15 ids)

All note lines kept short (<1.5k chars) to stay far below the 2000-char
read-tool line cap (line-cap truncation corrupted earlier revisions).
Ids/owners/dependsOn unchanged; only ABC-strength id = F4.c.cardP-ABC-strength.
Data only; no sorry/axiom/True/PUnit. -/

namespace LeanFormal.IUT.Audit

def S3131FinalResidualRegistry : List Obligation :=
  [
  { id := "R1.M0.native-to-OriginalInput"
    source := "IUT I Definition 3.1 (I-T.txt:3122)"
    status := VerificationStatus.pending
    note := "OWNER shehdd (S3134 bridge; reduced to S3134SameCContractBridgeEpsilonResidual). Native T <-> OriginalInput record identification. NOT ABC-strength. DEPENDS: none. OVERLAPS: cusp same-C id."
    dependsOn := [] },
  { id := "R1.M1.bad-tensor-index"
    source := "IUT I Def 3.1(b),(e); III Prop 3.4(ii)"
    status := VerificationStatus.pending
    note := "OWNER qpilot (S3131BadTensorIndexEquivalence green Prop; construction missing). Bad <-> C3.tensorIndex. NOT ABC-strength. DEPENDS: R1.M0."
    dependsOn := ["R1.M0.native-to-OriginalInput"] },
  { id := "R1.M2M3M5.sameC-q-theta-readout"
    source := "IUT I Ex 3.2(iv); II Rem 2.5.1(i); III Prop 3.4(ii); IV Prop 1.4(i)"
    status := VerificationStatus.pending
    note := "OWNER lattice. CANONICAL object = SameCModelMapResidual/SameCQThetaReadoutBridge. M0/M3 PROVED (qpilot minimal); residual = M1 + M2b (M2a CLOSED per Lead/lattice: M2a CLOSED (Lead-verified second real closure): S3133M2aClosedActual EXIT0 SIZE=5173 + S3133M2aNormReductionActual EXIT0 SIZE=3200, checker CITABLE (6/2 real decls, probe_ok; no sorryAx; trio probes; S3133RationalFiveCompletionNorm_holds + S3133GaussianCanonicalQNorm_holds)); prior M2 structure: M2a refined node S3133RationalFiveCompletionNorm exact Missing base completion norm, reduction S3133GaussianCanonicalQNorm_of_rationalCompletionNorm; M2b S3133GaussianClauseBDescent clause-B/Tate-q descent D4 (qpilot S3133M2bAttackActual EXIT0 + _S3133Batch24 trio: proved S3133M2b_clauseB_witness, S3133M2b_QCSource_qV, S3133GaussianClauseBDescent_of_tateQIdentification; exact missing spec S3133M2bTateQIdentification {q : Completion concreteGaussianFivePlace; q_norm = 1/5; descent : forall b above 5, norm(qVFamily b) = norm q}, documented insufficiency: generic SourceClauseB has no norm value, q_v=1/5 is paper chosen datum D4 IUT I Def3.1(b)/Ex3.2(iv), II Rem2.5.1(i), III Def3.8(i); qpilot S3133R1StatusNoteActual EXIT0 gives S3133R1M1Node/M2aNode/M2bNode + proved S3133R1M2aNode_imp_canonicalQ, probe trio) with S3133GaussianClauseBDescent_of_atBase + S3133GaussianQParameterMatchAtBase_of_ClauseBDescent_and_canonicalQ). M0/M3 proved; M4 raw negative + normalized total-one; M5 normalized adapters proved. WARNING: do NOT import LeanFormal.IUT.Foundations.AlgebraicGeometry.BaseScalarValuationRelation (quarantined compile errors). Sub-ids INDEX.R1.M2.base-q-transport, INDEX.R1.M2.clause-B-descent; M2a refined S3133RationalFiveCompletionNorm, M2b S3133GaussianClauseBDescent. NOT ABC-strength. DEPENDS: R1.M0, R1.M1. MODEL-ROUTE (Option B, third combined reopen): REUSED in-tree concrete model (SourceUnitRegionHaarDataActual: sourceHaarActualOriginalInput/ImageRealization/Data). Model-route evidence: M1 in-model constructible (S3133ExistingModelAdaptationActual, S3133ModelM1PlaceToModActual); M2b definitional in-model (descent = rfl); F4 by construction from class-B data (S3135ValueMonoidRealifiedIdentification + s3135_compatibility_of_realifiedIdentification; S3135ProcessionScalingUnitDatum + s3135_procession_scaling_unit_degree_zero; s3135_actualF4_of_realifiedIdent_and_processionDatum); nontrivial scaling witness baseUnit = -1 with norm 1 and mu((-1)*O) = mu(O) (s3135_modelHaar_negOne_scaling_eq). UNCHANGED: F4.c.cardP; abstract-contract M1/M2b (class B/C per A23); paper-route (b) RegionRelativeToHullAndWeight + finite hull/region volume; (c) uniform height-vs-volume comparison (A26); 15 ids/order/ABC; no v4."
    dependsOn := ["R1.M0.native-to-OriginalInput", "R1.M1.bad-tensor-index"] },
  { id := "R2.absNorm-rational-place"
    source := "IUT III Rem 3.1.1(ii) (corpus 5408-5465); Mathlib absNorm"
    status := VerificationStatus.pending
    note := "OWNER mainline. absNorm (comap place).maximalIdeal.asIdeal = Rat.HeightOneSpectrum.natGenerator (tree half qVFamTensorP = natGenerator rfl). Chain: absNorm_apply -> Submodule.cardQuot_apply -> Nat.card_congr (Ideal.quotientEquiv along Rat.ringOfIntegersEquiv; hIJ: span = map) -> absNorm_span_singleton -> simp. NARROW, not ABC-strength."
    dependsOn := [] },
  { id := "R2.nu-generator-exponent"
    source := "Example36LocalIdealValuation; IUT III Rem 3.1.1(ii)"
    status := VerificationStatus.pending
    note := "OWNER mainline. completionValuationExponent v (mk0 qVFamNormalizedGenerator) = (qVFamily T b).exponent. Plan: unfold completionValuationExponent + completionValuationAdd_eq_log; Units.val_mk0; WithZero.exp/log bridge. NARROW, not ABC-strength."
    dependsOn := [] },
  { id := "canonical.normalized-2l-root-supply"
    source := "IUT I Ex 3.2(iv); II Introd. pp.2-3; III Def 3.8(i) p.112; Rem 3.1.1(ii); IV Prop 1.4(i)"
    status := VerificationStatus.pending
    note := "OWNER mainline. Exact type: Nonempty (ArithmeticTuplePureFractionalScalingData (qVFamTensorPlaces T b) qVFamTensorTuple (rootHalfCoefficient T b)) = actual chosen q_v^(1/2l) at c_norm/(2l); blocks numeric Q_C=-|log q| (convention only). ROOT-EXISTENCE TOOLS (existing; stage4 instantiated UNCONDITIONALLY): LeanFormal.IUT.IUTII.Kummer.NatRootSystem.rootSystemOfAlgClosed + Brauer.KummerH2.exists_root (alg-closed, n>0); S3136LGPToolReuseRootActual builds lgpAlgClosedRootSystem/lgpAlgClosedTwoLthRoot (+_pow/_exists/_brauer; ratio_mem_mu = mu_2l) for the actual q_v unit; same instantiates for qVFam normalization unit. ContinuousKummerTheory/Kummer/PAdic: padicKummerZHatEquiv + finite Kummer quotients. REDUCED MISSING = normalized reading of the root in the completion (extension/ramification norm comparison, same as R2) + fractional-coefficient integrality (norm group p^Z). S3131RootSupplyToolProbeActual checks imports/axioms. NOT ABC-strength. DEPENDS: R2.absNorm, R2.nu."
    dependsOn := ["R2.absNorm-rational-place", "R2.nu-generator-exponent"] },
  { id := "ThetaHalf.vform-canonical-residual"
    source := "IUT III Prop 3.9(i) p.115; Rem 3.9.5(i); Cor 3.12; IV Prop 1.4(i)"
    status := VerificationStatus.pending
    note := "OWNER hull (GREEN). = ThetaHalfVFormCanonicalResidual/MissingVFormCanonicalIdentification. Refined: (1/d)(log mu(hull)-log mu(O_hol)) = S3131CanonicalRootedHC T mu (S3132VFormMassRestatementActual 6542; probe missingVFormCanonicalIdentification_iff_haar_mass_eq trio). Transport dependency task-62/65: index half numerical (S3132UniformIndexConstructibleActual 145108) -> fiber DATA-ONLY ActualPlaceDataForC3 (comap_eq + Iut.ThetaFinitePlace.completionRingHom bijective = e=f=1; MissingFiberCompletionComparisonAt, S3132FiberExternalCompletionBridgeActual 146723; repo bridge 146557; probes trio; NO missing mathematics) -> transport (S3132UniformFactorComparisonComponentActual 139226; missingData_iff_pair 145441) -> Theta-half; NEW GREEN hull S3132ConcreteGaussianPlaceSpecActual EXIT0 (concrete Gaussian place spec; potential route to instantiate ActualPlaceDataForC3; 5 decls trio; remaining: surjectivity/dimension step + model tie). placeToMod provenance absent from all libs; all-v task-38 form over-strong (place-restricted faithful). NOT ABC-strength. DEPENDS: R1.M0."
    dependsOn := ["R1.M0.native-to-OriginalInput"] },
  { id := "ThetaHalf.exact-factor-residual"
    source := "IUT III Prop 3.9(i) p.115; Rem 3.9.5(i); Cor 3.12; IV Prop 1.4(i)"
    status := VerificationStatus.pending
    note := "OWNER hull (GREEN). = ThetaHalfExactFactorResidual. factor=0 iff (d-1)log mu(hull)+log mu(O_hol)=0 (d=finrank_Qp of C3 tensor block); label-level d=1 iff mu(O_hol)=1; composition (d=1, mu(O_hol)=1, V-form) => MissingCanonicalRootedThetaReadout (S3132ThetaFactorZeroConditionActual 6784; probe canonicalTarget_iff_log_haar_eq_of_finrank_one_unitReference trio). Reductions S3132SharperThetaTargetReductionActual 7210: canonicalTarget_iff_factor_eq/_factor_zero_of_VForm/MissingCanonicalRootedThetaReadout_of_factor_zero_and_VForm. Normalization channel files 138375/143978/144129. Raw consumer ThetaHalfRawResidual folded. NOT ABC-strength. DEPENDS: ThetaHalf.vform-canonical-residual."
    dependsOn := ["ThetaHalf.vform-canonical-residual"] },
  { id := "ThetaHalf.canonical-q-formula-gap"
    source := "IUT III Rem 3.1.1(ii); III Prop 3.9(i); S778 per-b formula"
    status := VerificationStatus.pending
    note := "OWNER shehdd (S3134CanonicalQFormulaGap) = consumer of canonical.normalized-2l-root-supply. Conditional scalar Q_C=-|log q| only; no numeric claim. NOT ABC-strength."
    dependsOn := ["canonical.normalized-2l-root-supply"] },
  { id := "F4.a.value-group-splitting"
    source := "IUT IV section 2 (corpus 2329-2332); F4 clause (a)"
    status := VerificationStatus.pending
    note := "OWNER abc. F4.a = hpt (S3135PointLogShellFaithfulness) of the gate. Conditional artifact s3135_finalAssemblyGateV3 => ABCConjecture (S3135GateHypothesisAuditActual; s3135GateHypothesisTable). Exact missing S3135ValueMonoidIdentification. Sub-id INDEX.F4.a.value-monoid-identification. TOOLS referenced: S3137ToolInventoryIndexActual TOOL.* ids; TOOL.piTensorCongr S3139ToolsTensorCongrLaws; TOOL.realUnitCharacter S3139ToolsRealUnitCharacter. NOT ABC-strength."
    dependsOn := [] },
  { id := "F4.b.paper-scaling-zero"
    source := "IUT IV section 2 (corpus 2329-2332); F4 clause (b)"
    status := VerificationStatus.pending
    note := "OWNER abc. F4.b = hzero (S3135ScalingLogDegreeZero). b1 modulus: pushforward half CLOSED (S3135HaarUniquenessToolActual CITABLE: s3135_addHaar_eq_smul generic two-Haar tool from Measure.isAddLeftInvariant_eq_smul, s3135_haar_pushforward_eq_smul_actual, s3135_haarUniquenessScalarStep_proved : S3135HaarUniquenessScalarStep PROVED; S3135HaarPushforwardActual + S3135HaarIndexActual citable); ONLY missing remains S3135LogShellScalingIndex (hidden residual count -1; abc S3135LogShellIndexRouteActual routes the remaining S3135LogShellScalingIndex; strategic shortcut: unit self-similarity may drop (b) WITHOUT the index computation (logDegree 0 => lambda unit => lambda*O = O => mu set equality)); b2 missing record; b3 S3135ScalingNormalizationActual. 5 sub-nodes (INDEX.F4.b1/b2/b3; parent-map row 5). NOT ABC-strength."
    dependsOn := [] },
  { id := "F4.c.cardP-ABC-strength"
    source := "IUT IV section 2 (corpus 2329-2332); F4 clause (c)"
    status := VerificationStatus.pending
    note := "OWNER abc. F4.c = hP = F5 card P of the gate; EXACTLY ABC-strength by tightness (card P <=> ABCConjecture). Exact missing ABCHeightWeightAdditiveBoundV2. THE ONLY ABC-STRENGTH RESIDUAL; all others narrower. DEPENDS: F4.a, F4.b."
    dependsOn := ["F4.a.value-group-splitting", "F4.b.paper-scaling-zero"] },
  { id := "LGP.residuals"
    source := "IUT II/III LGP construction"
    status := VerificationStatus.pending
    note := "OWNER stage4. 17 INDEX.LGP.* sub-ids (parts 2/4/7; e.g. INDEX.LGP.local-o-lattice-quasi-lattice, INDEX.LGP.bad-weight-qpilot-comparison). Component residuals; NOT ABC-strength; NEW GREEN stage4 LGPJvQSpanTop2 EXIT0 (J_v/Q-span top-2)."
    dependsOn := [] },
  { id := "first-triangle.A-C"
    source := "IUT III first triangle (Step (xi) structure)"
    status := VerificationStatus.pending
    note := "OWNER stepxi. Conditional integration GREEN: S3139FirstTriangleIntegrationActual.firstTriangleConditional (+_qPilot/_gluing_invariance EXIT0 143612); FirstTriangleRemainingResidual {infinitePlaceChoice, sourceCapsuleData, sameCIdentification, placeSelection}; consumer record FT.* ids. 13+ INDEX.first-triangle.* sub-ids; FIRST-TRIANGLE UPDATE (Lead-approved single re-pin edit): FT.C1.infinite-place-choice RESOLVED (S3139C1InfinitePlaceActual.sourceInfinitePlaceChoice_nonempty/_Actual/sourceArchimedeanScalarActual/sourceArchimedeanRealification_nonempty, 148946); FT.C3.ind1-bridge-dependency DISCHARGED (S3139C3Ind1BridgeActual.sourceInd1BridgeDependency_Real_holds, 149009); FT.C3.convention-identification PROVED/CLOSED: sourceInd1ConventionIdentification_holds (S3139C3ConventionClosureActual, EXIT0, checker CITABLE: olean fresh/decls 3/probe_ok; probe trio-only for sourceInd1ConventionIdentification_holds, sourceInd1ConventionComparison_tprod, piTensorEntryPermute_tprod, polyIsoOfPerm_tensorMap_tprod, PrcAutomorphismTensorAction_tprod; generic tool piTensorEntryPermute; paper convention kept); circularity audit citation: task-68 S3140CircularityAuditActual (checker CITABLE) + mainline Appendix A/A9/A11 (no proof circularity); III:604-620 Fig. I.4-I.6; probe _S3139C1C3Probe 149134 trio. Remaining: C3 convention identification + cross-stream M0/M1 + stage4 unit map. C2 update (stepxi): FT.C2.kummer-artin-pairing is now a THEOREM (S3139C2KummerArtinTheoremActual.sourceKummerArtinPairingCompatibility/_nonempty/sourceKummerArtinPairing_eq; Brauer pairing reuse PadicField.pairingH1_kummer); FT.C2.galois-kummer-compat RESOLVED/superseded (SourceKummerArtinCompatibility removed from missing list; negative hom-level node retained, not promoted); FT.C2.hom-level-refuted negative route recorded (not promoted); TOOL.brauer-pairing = PadicField.pairingH1_kummer; probes trio (_S3139KummerArtinProbe 148545, _S3."
    dependsOn := [] },
  { id := "cusp.same-C-id"
    source := "IUT I Def 3.1 tuple/f clause (I-T.txt:3123-3126, :3273-3282)"
    status := VerificationStatus.pending
    note := "OWNER shehdd (NativeCuspParameterMissing constructed as eps; residual = S3134SameCContractBridgeEpsilonResidual record equality). OVERLAP: same bridge as R1.M0. NOT ABC-strength."
    dependsOn := ["R1.M0.native-to-OriginalInput"] },
  ]

#check S3131FinalResidualRegistry

end LeanFormal.IUT.Audit