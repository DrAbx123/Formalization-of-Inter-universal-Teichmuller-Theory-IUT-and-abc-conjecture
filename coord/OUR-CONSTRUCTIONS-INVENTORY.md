# OUR-CONSTRUCTIONS-INVENTORY — paper-faithful construction stacks in tmp/sheaf/xif/paper

Status: READ-ONLY inventory, 2026-11-12. No Lean file written, no compile.
Olean = .lake/build/lib/lean/tmp/sheaf/xif/paper/<file>.olean exists now.
Green source = file has an olean and its declarations are used as green in the
existing ledger; "model/conditional" means the file proves an arithmetic/model
interface, not the lana/paper actual object.

## 1. Step V stack (IUT IV Thm 1.10 Steps (iv)-(v))

| file | key declarations | olean | dependencies | status/paper step |
|---|---|---|---|---|
| Mzk1PaperStepVBoxActual.lean | paperLHS/paperRHS; paperRHS_expand; paperStepV_inequality; paperBoxRHS; paperStepVRows | TRUE 640480 | Mathlib only | green arithmetic model of the Step V box; not an actual hull; Step (v) |
| Mzk1StepVPaperActual.lean | stepV_paperForm_le; stepV_paperForm_le_l; stepVPaperRows | TRUE 70440 | LeanFormal.IUT.IUTIV.Estimates.StepVProcessionAverage + Mathlib | paper-form Step V estimate; condition on real parameters; Steps (iv)-(v) |
| Mzk1StepVIdentificationActual.lean | StepVDictionary; volume_upper_of_dictionary; PaperDictionaryShape | TRUE 168672 | Mzk1StepVVolumeUpperActual | dictionary connecting Step V expression to volume upper; model |
| Mzk1StepVVolumeUpperActual.lean | paperBox/stepVExpr/stepVRHS; volume_upper_of_stepV; volume_upper_of_identification; box_coefficient_shape | TRUE 166056 | Mathlib | volume upper bound interface from Step V; model |
| Mzk1VStepVAlignmentActual.lean | vStepVRows; vStepVRows_length | TRUE 32208 | Mathlib | alignment ledger only (no analytic theorem); audit |
| S3014StepVProcessionAverageActual.lean | S3014PerLabelBound; S3014ProcessionAverageBound; S3014_processionAverage_le; S3014ProcessionData | TRUE 239848 | LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceStepVLambda | paper procession/j-average arithmetic; Step (v) |
| S3016StepVQPilotIdentificationActual.lean | S3016StepVQPilot; S3016WeightedGlobalQPilot; S3016IdentificationTarget/Gap | TRUE 15904 | NativeGlobalQPilotNormalizedLogVolume, S2736, S2752, S2771 | q-pilot identification target; Step (v) bridge |
| S3016CThetaUpperActual.lean | S3016CThetaUpperInterface; stepV_eq_global; upper_bound | TRUE 118040 | S3016StepVQPilotIdentification, S2959HalfIQHullCThetaUpper, NativeQPilot | CTheta upper interface; Step (v) |
| S3017StepVUpperGapAssembly.lean | S3017_processionAverage_bound; expanded; S3017_CTheta_upper_of_height | TRUE 48664 | S3014, S3015FinalRealInequality | gap assembly; Step (v)-(vi) |
| S3019StepVQPilotIdentificationProofActual.lean | S3019_target_iff_log_sum; S3019_identificationTarget_iff_sum; S3019MissingBridge | TRUE 34872 | S3016, NativeGlobalQPilot, S2736 | conditional proof of q-pilot identification; missing bridge is named |
| S3029StepVAlignmentActual.lean | S3029DifferentTerm/ExceptionalTerm/StepVTerm; S3029_perLabel_decomposition/affine; S3029AlignmentData | TRUE 469520 | S3014, S2921HeightBridge | per-label decomposition; Step (v) |
| S3034PacketScalarBoundActual.lean | S3034Hscalar; S3034_hscalar_iff | TRUE 19720 | S3025, S2990, S2957 | packet scalar bound; Step (v) |
| S3034StepVAlignmentWitnessActual.lean | S3034AlignmentData; S3034_perLabel_affine | TRUE 73440 | S3029 | alignment witness; conditional data |
| S3050StepVQExpansionActual.lean | S3050Unit; S3050QCoeff; S3050LabelRest; S3050_stepVTerm_eq_qCoeff...; S3050QUnitIdentification | TRUE 94560 | S3029 | q-expansion coefficients; Step (v) |
| S3050ConnectedSite.lean | S3050ConnectedProperty/Scheme/Site/Q; S3050QIsPrestack/Stack/HomSheafCondition/DisconnectedObstructionExcluded | TRUE 35328 | S2844D6F6BaseChangeActual | geometric connected-site interface, not volume; separate subbranch |

Note: these are our own arithmetic/interface constructions; none constructs the
lana actual hull. They are "paper Step V shape" rather than a proof of IUT IV
Theorem 1.10.

## 2. D_exact stack (paper defect/gap route)

| file | key declarations | olean | dependencies | status/paper step |
|---|---|---|---|---|
| Mzk1DExactFromHullActual.lean | DExact; DExactWithArch; term_ge; tame_height_ge; L7_term; L7_global; L7_with_arch; l7Rows | TRUE 192664 | Mathlib | green exact-hull lower arithmetic; Step (xi)/D_exact |
| Mzk1DExactLowerActual.lean | L1ShellVolume; L2TameExponent; L3HullPacket; L4ProcessionAverage; L5CapsuleAverage; L6Assembly; DExactLowerTarget; l6Reduced_of_dExactLower; ssIneqExplicit_of_dExactLower; classicExceptionPrimes/records | TRUE 308600 | ThetaDataLegality, LocalVolumeAssembly, KappaLemma | conditional D_exact lower bound -> L6/SSIneq; Step (xi) |
| Mzk1PaperNormDeficitActual.lean | deficit_expansion; verdict_iff_deficit_nonpos; sum_logMuPaper_ge_odd/two; deficit_pos_witness; deficit_pos_no_diff; deficit_nonpos_iff | TRUE 147968 | PaperNormMu, PaperNormTheta | paper-normalized deficit arithmetic; Step (x)-(xi) |
| Mzk1PaperNormMuActual.lean | paperMuCoeff; logMuPaper; logMuPaper_ge_odd/two/le_base; PaperNormVerdict; paperNormDeficit; paperNormVerdict_iff_deficit_nonpos | TRUE 242048 | Mathlib | paper normalization coefficient/mu model; Step (xi) |
| Mzk1DeficitSignActual.lean | deficit_sign_aligned; diffPerPlace_recover_different; paperMuCoeff_p2_e1_r2_n1; logMuPaper_p2_e1_r2_n1 | TRUE 85104 | DifferentDictionary, PaperNormDeficit | sign alignment / dictionary; Step (xi) |
| Mzk1P2DeficitActual.lean | logMuPaper_2_r2_eq_neg_log2; logMuPaper_2_r1_eq_zero; deficit_pos_of_p2_r2; deficit_nonpos_of_p2_r1; logMuPaper_2_faithful_nonneg | TRUE 118592 | PaperNormDeficit, PaperNormMu | p=2 deficit case study; sign/model |
| Mzk1DifferentDictionaryActual.lean | log_norm_differentGenerator_eq_neg_paperOrder_mul_log; diffPaperLog; diffPaperPerPlace; torsionConstant; archConstant; differentRows | TRUE 167264 | LeanFormal LocalDifferentNormOrder, IntegralLogShellSharpBounds | dictionary from different/log to paper terms; Step (x)-(xi) |

Known ledger status (AUDIT_LEDGER A788-A805): PaperNormMu/PaperNormDeficit/
DifferentDictionary are green arithmetic; deficit_pos_witness is explicitly a
non-faithful witness; the faithful convention makes deficit < 0 (no
counterexample) and the sign/normalization identification with -|log Theta| is
still the top open item. These files do not prove the paper's D_exact bound
unconditionally.

## 3. Volume/hull stack

| file | key declarations | olean | dependencies | status/paper step |
|---|---|---|---|---|
| Mzk1LocalVolumeAssemblyActual.lean | logMuPaper; tameShellExponent; hullPacketShape; avgJPlusOneShape; avgJSquareShape; assembledVolume; volume_eq_assembled | TRUE 160208 | Mathlib | green local volume assembly arithmetic; Step (v)-(xi) |
| Mzk1ThetaDataLegalityActual.lean | ThetaDataLegality; l_not_dvd_e_of_legality; ShellAssembly; DExactLowerBound; L6ReducedInequality; paperGap_of_legality_and_DExact; legalityRows | TRUE 282088 | Mzk1PrimeConductorRouteActual | legality/interface to D_exact; Step (xi) |
| Mzk1KappaLemmaActual.lean | sL; AL; SSIneqKappa; kappa_factor; kappa_bound; ssIneqKappa_one | TRUE 159816 | Mathlib | green kappa normalization arithmetic; Step (xi)/SS |
| Mzk1SSIneqExplicitFormActual.lean | SSIneqExplicit; ssIneqExplicit_iff_kappa; ssIneq_of_sigma_bound; ssIneq_of_half_volume; explicit instances | TRUE 164936 | Mathlib | green explicit SSIneq form; not a proof of SS |
| Mzk1VolumeUpperActual.lean | volume upper interface/rows | TRUE 202504 | own volume ledgers | green model/audit; paper upper bound |
| Mzk1VolumeUpperLeActual.lean | volume upper ≤ form | TRUE 174992 | own volume ledgers | green model; paper upper bound |
| Mzk1VolumeEstimateQpilotActual.lean | q-pilot volume estimate | TRUE 81240 | own qpilot/volume | green conditional estimate |
| Mzk1VolumeIdentificationActual.lean | volume identification | TRUE 129168 | own volume/qpilot | green identification interface |
| Mzk1VolumeUpperAuditActual.lean | volume upper audit rows | TRUE 141968 | own volume | audit/ledger |
| Mzk1VolumeIdentificationAuditActual.lean | volume identification audit | TRUE 153712 | own volume | audit/ledger |
| Mzk1VolumeIdentificationAuditShaActual.lean | SHA audit | TRUE 220240 | own volume | audit/ledger |
| Mzk1VolumeRealActual.lean | real volume readout | TRUE 15784 | own volume | green readout |
| Mzk1SignedLogVolumeActual.lean etc | signed log volume family | mixed | own qpilot/volume | see individual olean column |
| Mzk1HullLogVolumeFormulaActual.lean | hull log-volume formula | TRUE 243816 | own hull | green formula interface |
| Mzk1HullVolumeReuseActual.lean | hull volume reuse | TRUE 143816 | own hull | reuse/ledger |
| Mzk1ShellVolumeUpperBoundActual.lean | shell volume upper bound | TRUE 240240 | own shell/volume | green upper bound |
| Mzk1GlobalPositiveThetaHullLogVolumeActual.lean | global positive theta hull volume | TRUE 156768 | own hull/global | green interface |

There are ~200 files matching Mzk1Volume*; the table lists the construction
chain used by the C-line, not every audit/consumer file. Most have olean TRUE;
files without olean are marked absent in the filesystem listing and are not
counted as green.

## 4. Q-pilot and L-carrier stack

| file | key declarations | olean | dependencies | status/paper step |
|---|---|---|---|---|
| OrigXiFPaperQPilotFromSourceLActual.lean | OrigXiFPaperQPilotOfBoundary; ..._boundary/strip/oneColumn/lineBundle/logKummer/qPilotLogVolume/data; OrigXiFSourceLLineBundleCarrier; OrigXiFQPilotLogVolumeIdentification; OrigXiFThetaPacketIdentification | TRUE 147176 | S1391, PaperQPilotObject, PaperQPilotObjectSourceActual, OneColumnFinitePrimePlaceActual, ArithmeticQPilotLogVolume | green actual L paper q-pilot object; paper Definition 3.8(i)/(1,0) q-pilot; four identifications remain explicit props |
| Mzk1QPilotLineLActual.lean | QPilotLineActualL; .core; .qScalar; qScalar_neg; PaperQPilotObjectActualL; QPilotIdentificationActualL; qPilotIdentificationActualL_nonempty_of_object; qPilotLCarrierRows | TRUE 180024 | QPilotObjectActual, S1391 | A947 PASS, parametric/interface; C1/C2 OPEN; not actual q-pilot |
| Mzk1SPaperQPilotIdentificationsActual.lean | sPaperQPilotObject; sPaperQPilotObject_qPilotLogVolume; sPaperQPilotObject_nonpos; sPaperRows | TRUE 58336 | OrigXiF...SourceL, OrigXiF...ObjectActual, IPLAPTDataActual, A946, QPilotLogNonpos | A956 PASS; fills OrigXiFPaperQPilotObject four fields (strip/lineBundle/logKummer/qPilot log); parametric on boundary b |
| Mzk1C3LogShellTensorLActual.lean | C3LogShellPlaceL/FiberL/BlockL; actualC3LogShellDatumL; actualC3LogShellL; actualC3LogShellTensorRegionL; compact; IQL; HaarL; logVolumeL; ActualC3LogShellTensorPacketL; actualC3LogShellTensorPacketL | TRUE 272200 | C3LogShellTensorPacketActual, S1391 | green L-carrier C3 tensor adapter; replaces old completion C3LogShellTensor; no concrete C3L term |
| S1487OQPilotScalarEqualityActual.lean | S1487Cand; S1487FivePlace; S1487W/Strip/Family/OriginalInput; S1487FaithfulSourceData; S1487FaithfulInput; S1487FaithfulC3; S1487FaithfulScalarEq; S1487TwoPlaceScalarNe; S1487Half... | TRUE 591240 | OrigXiFPaperQPilotScalar, OrigXiFThetaLink, LeanFormal ArithmeticQPilotBaseChange/ConcreteFinitePlaceBoundary/Example36.../ABCBridge | concrete S1487 SourceDefinition31Data + scalar calibration; NOT lana InitialThetaData/Cor312Variant instance |

Caveat for Q-pilot/L: Mzk1QPilotLineLActual is parametric (C1/C2 open);
Mzk1SPaperQPilotIdentifications is pass-parametric but b is not asserted
nonempty; OrigXiFPaperQPilotOfBoundary has five actual data fields but the four
paper_*_identification fields of the frozen object remain explicit obligations;
Mzk1C3LogShellTensorLActual has no concrete C3L term; S1487 is our concrete
source data/scalar, not a lana InitialThetaData.

## 5. Cross-stack dependency picture

Step V arithmetic stack:
  Mzk1PaperStepVBoxActual / Mzk1StepVPaperActual
    -> Mzk1StepVVolumeUpperActual
    -> Mzk1StepVIdentificationActual
    -> S3014 (procession average) -> S3017/S3029/S3034/S3050 (assemblies)
    -> S3016/S3019 (q-pilot identification; S3019MissingBridge named).

D_exact/sign stack:
  Mzk1PaperNormMuActual -> Mzk1PaperNormDeficitActual -> Mzk1P2DeficitActual
  Mzk1DifferentDictionaryActual -> Mzk1DeficitSignActual
  ThetaDataLegality + LocalVolumeAssembly + KappaLemma -> Mzk1DExactLowerActual
  Mzk1DExactFromHullActual is an independent arithmetic exact-hull lower form.

Volume/hull stack:
  local arithmetic (LocalVolumeAssembly, KappaLemma, SSIneqExplicitForm)
  + hull/volume ledgers (Mzk1VolumeUpper/Le/Identification/HullLogVolumeFormula...)
  -> Mzk1DExactLowerActual / SSIneq explicit consumer.

Q-pilot/L stack:
  S1391 SourcePilotRegionDataL
    -> Mzk1C3LogShellTensorLActual (C3 tensor adapter)
    -> Mzk1QPilotLineLActual (line/identification interface)
    -> OrigXiFPaperQPilotFromSourceLActual (paper q-pilot object)
    -> Mzk1SPaperQPilotIdentificationsActual (four fields)
  S1487OQPilotScalarEqualityActual supplies a concrete SourceDefinition31Data
  scalar calibration, separate from lana InitialThetaData.

## 6. Green/status summary

- GREEN (olean present, declarations used as green arithmetic/interface):
  all files in sections 1-4 with olean TRUE; notable PASS entries:
  Mzk1QPilotLineLActual (A947 PASS, parametric), Mzk1SPaperQPilotIdentificationsActual
  (A956 PASS), Mzk1C3LogShellTensorLActual (adapter), OrigXiFPaperQPilotFromSourceLActual
  (green object), S1487 (concrete source data, not lana instance).
- CONDITIONAL/MODEL (olean present but not a proof of the paper/lana actual
  statement): Step V box/volume upper, D_exact lower (conditional on DExactLower),
  paper deficit sign, volume upper/identification interfaces, SSIneq explicit.
- OPEN NAMED: S3019MissingBridge; Mzk1QPilotLineLActual C1/C2; b nonempty for
  SPaper; four frozen paper_*_identification props in OrigXiFPaperQPilotOfBoundary;
  concrete C3L term for C3LogShellTensorL; S1487 is not an InitialThetaData.
- Files without olean in the filesystem listing are not counted green; they are
  marked absent in the individual listings (e.g. Mzk1FinsetVolumeLawsActual,
  Mzk1GlobalQPilotVsSignedHullComparisonActual, etc.).

No Lean file written; no compile claimed.
