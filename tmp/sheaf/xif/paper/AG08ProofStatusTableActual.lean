/-!
# AG08: AG/GeometricCore/EtTh-Frd proof status table (data only; pins 14041)

Up-to-date proof status table for the bottom-up AG line and the external-object
targets (Lead order: AG bottom -> GeometricCore -> EtTh/Frd class A).

OWN LAYERS (stepxi; all EXIT=0 + checker CITABLE unless noted):
* AG02FunctionFieldActual (function field/vanishing order interface; Mathlib reuse).
* AG02bPrincipalDivisorActual (WeilDivisor as codim-1 coefficients; principalDivisor+mul).
* AG03DivisorsSectionsActual (O(D) Submodule of K(X); explicit CodimOneDVR hypothesis).
* AG03bSectionsBasicActual (restrict/mono/unit).
* AG04FiniteDivisorActual (finite-support divisors + degree; sections compatibility).
* AG04bResidueFieldActual (residue field at point; Mathlib ResidueField reuse).
* AG05CechActual (Čech/H0/H1 = L(D) on covers; A-class reuse of canonical adapted
  AG_FLT_Def_AlgebraicCurve_CechSectionsOfDivisor + Mathlib SheafCohomology; PENDING compile).
* AG06LineBundleActual (divisor/degree/Pic/ell/adeleBdd consumer; A-class reuse of
  AG_FLT_PromotionActual; PENDING compile).
* AG07MathlibCoverageActual (Mathlib/external coverage list; data).
CANONICAL EXTERNAL LAYER (qpilot owner; coord/EXTERNAL-PORT-REGISTRY.md):
* AG_FLT_PromotionActual: CITABLE 8 (degree_add/zero, mem_degZero_iff,
  isPrincipal_iff_mem, ell_nonneg, lSpace_mono, adeleBdd_mono, place_deg_nonneg).
* AG_FLT_Def_AlgebraicCurve_DivisorClassGroup (CITABLE 72), Repartitions,
  AdelicIndex (CITABLE 68), CoherentBaseChange, CechSectionsOfDivisor (canonical
  adapted module; queued/compiling).
* ported dirs: flt_core (SerrePairing/weilDualityAdelic/cechRiemannRoch/
  SmoothProperCurveFiniteMapData), flt_test (canonical divisor/Kaehler/RR-space),
  tauceti_rr (RiemannRoch/Pencil/Genus, Differential/CanonicalDivisor,
  WeilDivisor/SerdeDuality, Belyi/Basic) — feeding; promotions
  AG_FLT_RiemannRochPromotionActual / AG_TAUCETI_RiemannRochPromotionActual PENDING.
* DEPRECATED: stepxiAGRRFinishActual (my duplicate port; STOPPED per Lead/qpilot
  de-duplication decision; no imports from it).
GEOMETRICCORE ([Mzk1] Thm 2.5 input): statement layer GeomCore01StatementActual;
proofs to be wired from canonical Belyi/FiniteMapData promotions when green.
ETTH/FRD CLASS A: EtTh05FrobenioidBoundaryActual (EXIT0; concrete Frobenioid
boundary reuse), EtTh06ThetaQuotientActual (EXIT0; pre-realization quotient layer,
honest scope), Frd03ConcreteModelActual (EXIT0; concreteStageModel witness);
EtTh01/02/03/04 + Frd01/02 (CITABLE statement/reuse layers; deep inputs class B).
Honest: no layer above is claimed closed at paper level; deep [EtTh]/[Frd]/GenEll
results remain class-B named inputs.
**Component, not paper object.**  Registry frozen 14041; no registry edits.
No sorry/axiom/True/PUnit/toy carrier (data file).
-/

namespace LeanFormal.IUT.XiFPaper.AG08ProofStatusTableActual

/-- AG/external proof status rows: (layer, declarations, status). -/
def agProofStatus : List (String × String × String) :=
  [ ("AG02 function field", "AG02FunctionFieldActual", "EXIT=0; CITABLE (Mathlib reuse)"),
    ("AG02b principal divisor", "AG02bPrincipalDivisorActual", "EXIT=0; CITABLE"),
    ("AG03 O(D) sections", "AG03DivisorsSectionsActual", "EXIT=0; CITABLE (CodimOneDVR explicit)"),
    ("AG03b sections basic", "AG03bSectionsBasicActual", "EXIT=0; CITABLE"),
    ("AG04 finite divisors", "AG04FiniteDivisorActual", "EXIT=0; CITABLE"),
    ("AG04b residue field", "AG04bResidueFieldActual", "EXIT=0; CITABLE"),
    ("AG05 Cech/H0/H1", "AG05CechActual", "GREEN EXIT0 169705; COMPLETE proofs via canonical AG_FLT_CechPromotionActual (5 promoted) + CechSectionsActual/TwoChartCechActual + Mathlib SheafCohomology"),
    ("AG06 line bundles/O(D)", "AG06LineBundleActual", "GREEN EXIT0 167553; CITABLE 9; consumer of canonical AG_FLT_PromotionActual"),
    ("AG06b RR/Serde interface", "AG06bRRInterfaceActual", "GREEN EXIT0 167454; CITABLE 3; interface/data layer (canonical RR/Serde assets ASSUMED COMPLETE per Lead)"),
    ("AG07 coverage list", "AG07MathlibCoverageActual", "GREEN EXIT0 167773; data (Mathlib/external coverage)"),
    ("external promotion", "AG_FLT_PromotionActual (qpilot)", "CITABLE 8"),
    ("canonical ported dirs", "flt_core/flt_test/tauceti_rr (qpilot registry)", "ASSUMED COMPLETE per Lead gate correction; promotions AG_FLT_RiemannRochPromotionActual / AG_TAUCETI_RiemannRochPromotionActual PENDING"),
    ("GeomCore01 statement", "GeomCore01StatementActual", "GREEN EXIT0 06:41:21; statement-only (assembly gated per Lead)"),
    ("AG08 status table", "AG08ProofStatusTableActual", "GREEN EXIT0 167794 (refreshed)"),
    ("AG09 ids", "AG09IdsActual", "data (INDEX.AG.cech/.line-bundle/.RR-Serde-interface/.proof-status/.GEOMCORE.statement)"),
    ("AG10 canonical divisor/genus", "AG10CanonicalDivisorGenusActual", "EXIT0; A-class reuse of AG_FLT_CanonicalDivisorPromotionActual (complete proofs; conditional on paper RR rows)"),
    ("GeomCore02 input wiring", "GeomCore02WiringActual", "data/wiring; GeometricCore assembly GATED (finite-map ported module + RR/Cech/canonical assets green; Belyi pending)"),
    ("AG11 Serre pairing", "AG11SerrePairingConsumerActual", "EXIT0; A-class reuse of AG_FLT_SerrePairingPromotionActual (pairing value formula COMPLETE; residue theorem explicit class-B row)"),
    ("GChoice critical-in-target", "Mzk1GChoiceCriticalInTargetActual", "EXIT0; LAST unramified gate CLOSED: critical points 0/alpha2/alpha1 map into image target; gChoiceData_complete (all Mzk1GChoiceData fields PROVED)"),
    ("GChoice avoid/unramified canonical", "Mzk1GChoiceAvoidCanonicalActual + Mzk1GChoiceUnramifiedCanonicalActual", "EXIT0; avoids+card PROVED for Mzk1ScaleData/gPoly (gChoice_avoids/gChoice_card_lt/gChoiceData_of_avoids); unramified shape + infinity PROVED + critical-in-target reduction (finite gate named); canonical Belyi critical-values rows"),
    ("AG14 proved-theorems", "AG14ProvedTheoremsConsumerActual", "EXIT0; A-class consumers of AG_FLT_ProvedTheoremsPromotionActual (serre bijective/flip, weilDualityAdelic alg-closed, cechRR genus-reached; COMPLETE ported proofs)"),
    ("AG15 finite-map canonical", "AG15FiniteMapCanonicalActual", "EXIT0; data record: canonical FiniteMapData promotion + GeometricCore pointer wiring"),
    ("Mzk1Belyi canonical", "Mzk1BelyiCanonicalActual", "EXIT0; canonical TauCeti Belyi consumer (B_{m,n} eval/collapse/critical values/Belyification; STEP card collapse via canonical polynomial)"),
    ("S3183 hull/det consumption", "S3183HullDetConsumptionRecordActual", "data: S3182 -> S3180 consumer event recorded; H2 data residuals + H4 class-B boundary documented"),
    ("Scope split (A313)", "RestatedLemma22InterfaceActual.restatedLemma22Scope + AlgebraicNestedInductionInput; consumer design P1CompositeConsumerInputs (h24Base + algebraicNestedInduction)", "F=Q BASE-ONLY component delivered; full P1(Qbar) reduction NAMED (not complete); no closure claim"),
    ("Restated Lemma 2.2 interface (single source)", "RestatedLemma22InterfaceActual", "EXIT0 199972 SIZE 6012 CITABLE: Mzk1Lemma22Target (C-point, P1(Q), specialSet {inf,0,1})/Good/induction statement/target_of_induction/vocabulary aligned with abc RestatedLemma24; interface only (gate NOT PASSED)"),
    ("B3 2.4 finite-beta <-> Problem C BaseCaseProvider (A417)", "Mzk1Rational24BaseCaseBridgeActual", "EXIT0 5119 SIZE, CITABLE 7: baseCaseProvider_discharged (abc identity witness PROVED) + paperScopeLemma24Statement_of_provedBaseCase (only StepProvider named) + rational24_and_baseCase_proved; layer split recorded; NO closure; gate NOT PASSED"),
    ("rational 2.4 target (finite beta) bottom (A414)", "Mzk1Rational24TargetBottomActual", "EXIT0 5781 SIZE, CITABLE 11: Rational24TargetFiniteBeta PROVED from B1 fold via B2; BaseProviderRestatedFinite + corrected provider; old BetaAvoidingBelyiBaseInput refuted at beta=infty; restated base/conclusion finite-beta re-exports; F=Q finite-beta scope; NO closure; gate NOT PASSED"),
    ("Unconditional finite-beta consumer base (A402)", "Mzk1Consumer24AdapterUnconditionalActual", "EXIT0 10264 SIZE, CITABLE 12: FiniteBetaCorrectedBase PROVED from Problem A fold (betaAvoiding_all); unconditional h24BaseConcrete for finite beta (named BetaAvoidingBelyiBaseInput premise removed); infinity-beta spec repair recorded; P1CompositeConsumerInputs bundle + statement/target via F=Q target; finite-beta/F=Q scope; NO closure; gate NOT PASSED"),
    ("Problem D/E deep inputs in consumer (A398)", "Mzk1P1ConsumerDeepInputsActual", "EXIT0 8734 SIZE, CITABLE 11: ProblemDDeepInputs (precise witness Mzk1GeometricCoreRecastPrecise + line-bundle iso placeholder) + ProblemEDeepInputs added as explicit fields; conditional deep statements PROVED from F=Q target (antecedents not asserted); 11-row consumed/named split; NO closure; gate NOT PASSED"),
    ("2.4 base adapter wired into consumer (F=Q)", "Mzk1Thm25P1CompositeConsumerWiringActual", "EXIT0 5810 SIZE, CITABLE 7: wiredInputs_h24Base_eq/cvLaw_eq/supplied + wiredStatement_holds + p1CompositeRealConsumerTarget_wired; h24Base slot = h24BaseConcrete (named BetaAvoidingBelyiBaseInput), CV law slot PROVED; h22/AlgebraicNestedInductionInput/Moebius/CPointLift explicit parameters; NO closure; gate NOT PASSED"),
    ("P1 composite REAL consumer (F=Q)", "Mzk1Thm25P1CompositeConsumerActual", "EXIT0 9619 SIZE, CITABLE 12: p1CompositeRealConsumerTarget_rational (P1CompositeRealConsumerTarget PROVED at F=Q scope) + p1Composite_mapPoints_consumer_rational (2.2 o 2.3 inversion composition; C-point CV control; scope rational-only, full-Qbar reduction NAMED; binding HOLD; gate NOT PASSED"),
    ("Thm2.5 real consumer design (NOT PASSED)", "Mzk1Thm25P1CompositeConsumerDesignActual + Mzk1Thm25Binding* records", "DESIGN/STATEMENT: P1 composite 2.4 o 2.3 o 2.2 target with C-point critical values; h22/h24 binding is HISTORY ONLY (not closure; gate lacks real consumer + C-point unramifiedness); binding HOLD; gate NOT PASSED"),
    ("GeomCore03 gated assembly", "GeomCore03AssemblyActual", "GATED: GeomCorePaperInput (placeholder-flagged) -> output statement; A-class generic constructor geometricCoreDataOfFunction PROVED; canonical assets wired in data; no closure claim"),
    ("AG12 Cech Riemann-Roch", "AG12CechRiemannRochActual", "A-class COMPLETE ported proof consumer (flt_th cechRiemannRoch_of_genusReached; conditional exactly on paper genus-reached row + cover data)"),
    ("AG13 Weil duality adelic", "AG13WeilDualityAdelicActual", "A-class COMPLETE ported proof consumer (flt_core weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists; conditional on paper RR rows)"),
    ("deprecated", "stepxiAGRRFinishActual", "STOPPED (duplicate; no imports)"),
    ("GeometricCore", "GeomCore01StatementActual", "statement layer; proofs pending canonical promotions"),
    ("EtTh/Frd class A", "EtTh05/EtTh06/Frd03 (+EtTh01-04, Frd01-02)", "EXIT=0 (class A reuse) / CITABLE statement layers"),
    ("deep inputs", "EtTh02DeepInputsActual; FrdI-II class B; GenEll Thm 2.1 (ii)=>(i)", "class B; proved := false") ]

end LeanFormal.IUT.XiFPaper.AG08ProofStatusTableActual
