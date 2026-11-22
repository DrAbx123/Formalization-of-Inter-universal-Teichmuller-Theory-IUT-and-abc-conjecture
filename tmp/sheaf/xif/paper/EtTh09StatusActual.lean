/-!
# EtTh09StatusActual — [EtTh]/[Frd]/AG/Mzk1 build-status record (data/ids only; pins 14041/23066/18800)

Consolidated status record of the stepxi-authored layer at this checkpoint (all cited
files are EXIT=0 + checker-CITABLE unless marked otherwise; no registry edits).
Honest split: COMPONENT/conditional vs paper-level rows; no closure claims.

STEP 0: status aggregation only (no new mathematics); consumers: mainline inventory,
lattice INDEX, lead gate.  Every evidence row carries its results.log line/sha where
recorded.  No sorry/axiom/True/PUnit/toy carrier (data file).
-/

namespace LeanFormal.IUT.XiFPaper.EtTh09StatusActual

/-- Build-status rows: (asset, declarations/evidence, status). -/
def etTh09StatusRows : List (String × String × String) :=
  [ ("EtTh07ConcreteBridgeActual", "EtThConcreteBridgeLevel, etThConcreteBridgeLevel, etTh_sourceModel_eq_boundary_model, etThConcreteBridge_sourceFrobenioid_eq_boundary, etThThetaLogVolume/Scale, etThConcreteBridgeReuse", "EXIT0 170963 SIZE 4481; checker CITABLE 6 (src F3E5F58E); concrete EtaleTheta bridge A-class reuse"),
    ("H4HullThetaCertificateActual", "h4_iqHullRealVolume_le, h4_hull_logVolume_le, h4_exists_hull_eq_ofReal, h4_ofReal_le_theta_of_imageSet_lower, h4_nonempty_iff, h4_cor312Conclusion, h4Status", "EXIT0 170655 SIZE 4399; checker CITABLE 7 (src 01DD2FB7); complete-proof H4 hull<=theta consumer of frozen Card-AMPL supply"),
    ("AG06bRRInterfaceActual", "AGRiemannRochInterface, ag_rr_functionFieldRiemannRoch_of_duality, ag_rr_weilDuality_of_index_adelic, agRRPromotionRows, agRRCanonicalAssets, agRRStatusHonesty", "EXIT0 171747 SIZE 5831; checker CITABLE 6 (src 07D4CAF2); consumes canonical AG_FLT_RiemannRochPromotionActual"),
    ("AG10CanonicalDivisorGenusActual", "ag10CanonicalDivisor(+_apply), ag10CanonicalClass, ag10Genus, ag10_ell_canonicalDivisor_eq_genus, ag10_degree_canonicalDivisor_eq, ag10Reuse", "EXIT0 175974 SIZE 4456; checker CITABLE 4 (src 5FC39EC7)"),
    ("AG11SerrePairingConsumerActual", "ag11ResidueTheorem, ag11SerrePairing, ag11SerrePairing_apply_mk, ag11SerdeReuse", "EXIT0 176541 SIZE 3857; checker CITABLE 3 (src D31BC090)"),
    ("AG12CechRiemannRochActual", "ag12_cechRiemannRoch, ag12Reuse", "WRITTEN+QUEUED (no dispatch yet; A-class consumer of ported complete-proof cechRiemannRoch_of_genusReached)"),
    ("AG13WeilDualityAdelicActual", "ag13_weilDualityAdelic, ag13Reuse", "WRITTEN+QUEUED (no dispatch yet; A-class consumer of ported complete-proof weilDualityAdelic reduction)"),
    ("GeomCore02WiringActual", "geomCoreInputWiring, geomCoreWrapperPolicy", "EXIT0 175892 SIZE 3429; checker CITABLE 2 (src 42CC1337); GeometricCore assembly GATED"),
    ("GeomCore03AssemblyActual", "GeomCorePaperInput, GeomCoreOutputStatement, GeomCoreAssemblyStatement(+_iff), geometricCoreDataOfFunction(+_nonempty), geomCore_conditional, geomCoreCanonicalAssets, geomCoreAssemblyPlan, geomCoreRemainingDischarge", "EXIT0 177427 SIZE 8622; checker CITABLE 11 (src 680DFECF); GATED assembly; Mzk1 placeholder flagged"),
    ("Indet06H7Ob9WiringActual", "H7Ob9IndetWiring, h7Ob9IndetWiring, h7Ob9_comparison_ind1_invariant/_ind2_invariant/_ind3_one_sided, h7Ob9ConsumerInterface", "EXIT0 178623 SIZE 5555; checker CITABLE 5 (src FFA2835D); consumed by hull Hull10H7Ob9ConsumerActual"),
    ("Mzk1Lemma22StepConstructionActual", "card_image_lt_of_not_injOn, card_image_lt_of_collision, p1_zero_ne_one, lemma22Step_card_lt, lemma22StepOfData, lemma22StepOfPoly, lemma22Step_exists, lemma22StepExists_packaged, lemma22Step_compose, lemma22StepObligations, lemma22StepCorpusRefs", "EXIT0 178999 SIZE 11968; checker CITABLE 11 probe_ok olean_fresh (src 41307B6D/olean 154568 991B71FF); probe _Mzk1StepProbe 179056; (b) STEP CONSTRUCTION CLOSED"),
    ("S3180ConditionalAssemblyActual", "Cor312AssemblyInputs, toContract, cor312_conditional, abcConjecture_conditional, IUTMainTheoremShape, iutMainTheorem_conditional, conditionalAssembly_with_hullDet, field/dep/audit ledgers", "EXIT0 176409 SIZE 13521; checker CITABLE 11 (src 1E644472); shehdd FINAL PIN (non-gate/non-closure)"),
    ("Mzk1Cor31Cor32ProofActual", "finite_subcover_of_isCompact, cor31_finite_subcollection, isCompact_prod_set, cor32_finite_subcollection, cor31_reduction, cor32_reduction, wiring/status", "EXIT0 173956 SIZE 8521; checker CITABLE 10 (src B11FFF68); (b) Cor 3.1/3.2 A-class core"),
    ("S3182Cor312HullDetAssemblyActual (hull)", "HullDetAssemblyInputs, Cor312HullDetConclusion, cor312_hullDet_conditional, cor312_fieldScaling_component, cor312DeepStepRows", "hull GREEN/CITABLE (EXIT0 175469 SIZE 7091); consumed by S3180 conditionalAssembly_with_hullDet"),
    ("Hull08Ob9LogLinkActual (hull)", "HullOb9Inputs, hull_ob9_interface, hull_ob9_repClass_congr, hullOb9Rows", "hull EXIT0 178113; Indet05-level variant"),
    ("Hull10H7Ob9ConsumerActual (hull)", "HullH7Ob9ConsumerInputs, hull10_h7ob9_consumer, hull10_logLinkIterate_eq", "hull EXIT0 178789 SIZE 5584, checker CITABLE 5 (probe _Hull10ProbeActual 178834); consumes Indet06H7Ob9WiringActual"),
    ("Hull05WeightedIdentityActual (hull H2)", "weighted identity row", "hull CLOSED/CITABLE (H2/H4/H7 closed per lead)"),
    ("stage4 Mzk1Lemma22InductionActual", "Mzk1Lemma22PartialShape, partial_of_shape, comp_partial, mzk1Lemma22_partial_induction", "EXIT0 SIZE 4319 CITABLE 4 (mainline-verified); consumes lemma22StepExists_packaged for (b)"),
    ("GenEll/ABCBridge route", "GenEll09/10/11/14, S3171 display/inputs/height consumer, S3131 skeleton", "GREEN/CITABLE (earlier batches); (b)/(c) undilated interfaces; card P not assumed") ]

/-- Open gates (data): (gate, status, owner). -/
def etTh09OpenGates : List (String × String × String) :=
  [ ("full Lemma 2.2 chain rule -> StatementShape -> Thm25Wiring", "stage4: (a)(c)(d) done; (b) STEP CONSTRUCTION closed by Mzk1Lemma22StepConstructionActual; remaining: stage4 chain rule + Thm 2.5 wiring", "stage4/mainline"),
    ("Mzk1 Lemma 2.4 G/F/D/M items", "open (mainline gate v34)", "stage4/mainline"),
    ("H6", "PARTIAL", "mainline/stage4"),
    ("H5", "DONE (H2/H4/H7 closed)", "hull"),
    ("canonical big S_* proofs", "env-blocked (missing pinned-Mathlib olean.private; serial compile)", "qpilot"),
    ("AG12/AG13 dispatch", "queued, no dispatch yet", "stepxi"),
    ("L8", "frozen", "lead") ]

/-- Index ids (for lattice): (index id, declarations, file). -/
def etTh09Ids : List (String × String × String) :=
  [ ("INDEX.MZK1.step-construction", "Mzk1Lemma22StepConstructionActual: card_image_lt_of_not_injOn, card_image_lt_of_collision, p1_zero_ne_one, lemma22Step_card_lt, lemma22StepOfData, lemma22StepOfPoly, lemma22Step_exists, lemma22StepExists_packaged, lemma22Step_compose, obligations/corpus data", "Mzk1Lemma22StepConstructionActual.lean"),
    ("INDEX.INDET.h7-ob9-wiring", "Indet06H7Ob9WiringActual: H7Ob9IndetWiring, h7Ob9IndetWiring, h7Ob9_comparison_ind1_invariant, _ind2_invariant, _ind3_one_sided, h7Ob9ConsumerInterface", "Indet06H7Ob9WiringActual.lean"),
    ("INDEX.AG.cech-riemann-roch", "AG12CechRiemannRochActual: ag12_cechRiemannRoch, ag12Reuse", "AG12CechRiemannRochActual.lean"),
    ("INDEX.AG.weil-duality-adelic", "AG13WeilDualityAdelicActual: ag13_weilDualityAdelic, ag13Reuse", "AG13WeilDualityAdelicActual.lean") ]

end LeanFormal.IUT.XiFPaper.EtTh09StatusActual
