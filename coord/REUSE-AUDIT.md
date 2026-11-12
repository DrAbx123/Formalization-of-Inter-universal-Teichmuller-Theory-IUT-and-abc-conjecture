# REUSE-AUDIT — existing assets for current subgoals

Status: READ-ONLY grep, 2026-11-12. No Lean file, no compile.
Olean = .lake/build/lib/lean/<module>.olean exists now.
Availability classes:
  USE = olean present and exact statement reusable with no new math;
  ADAPT = olean present but needs sign/definition/interface adaptation;
  GAP = source only/no olean, or no existing theorem for the direction.

## 1. Sum j^2 / sFactor / qScaling

| need | existing file:theorem | olean | status | use |
|---|---|---|---|---|
| sum_{j=1..n} j^2 = n*sFactor | Mzk1ScalingNormalizationActual: sum_jsq_eq_nC_mul_sFactor | TRUE 255280 | USE | directly replaces a new ScalingNormalization sum identity |
| qScaling = -nC*sF*A | Mzk1ScalingNormalizationActual: qScalingNeg_eq_neg_nC_mul_sF_mul_A | TRUE | USE | direct q-scaling normalization |
| divided form | Mzk1ScalingNormalizationActual: qScalingNeg_div_nC_eq_neg_sF_mul_A | TRUE | USE | procession-normalized form |
| RemainingInequality / M_nonneg_of_remaining | Mzk1ScalingNormalizationActual: RemainingInequality, M_nonneg_of_remaining | TRUE | ADAPT | useful algebra, but depends on qPositiveSum being supplied |
| avg j+1 | Mzk1ProcessionAverageActual: avgJPlusOne_eq, avgJPlusOne_eq_l | TRUE 211768 | USE | Step V average coefficients |
| avg j^2 | Mzk1ProcessionAverageActual: avgJSquare_eq, avgJSquare_eq_l | TRUE | USE | Step V average coefficients |
| sFactor definition/average | Mzk1ShellArithmeticIdentitiesActual: sFactor, shell_average_identity | TRUE 153720 | USE | sFactor and shell average |
| sFactor = (n+1)(2n+1)/6 | Mzk1A763BoxAssemblyShaActual: sFactor_eq_sL | TRUE 317064 | USE | box coefficient comparison |
| sum_sq_range and box_szpiro | Mzk1A763BoxAssemblyShaActual: sum_sq_range, a763_box_szpiro | TRUE | ADAPT | box arithmetic; check exact RHS |
| LeanFormal elementary square sum | LeanFormal/.../ElementaryEstimates.lean: sum_Icc_one_sq_cast | source/olean? | ADAPT | alternative base sum; check module olean |

Conclusion: do NOT write a new ScalingNormalization file. Use Mzk1ScalingNormalizationActual
for sum/qScaling and Mzk1ProcessionAverageActual/Mzk1ShellArithmeticIdentitiesActual for
average/sFactor.

## 2. Signed log volume / signed volume / log volume

| need | existing file:theorem | olean | status | use |
|---|---|---|---|---|
| signed log-volume definition | Mzk1SignedLogVolumeCor312Actual: signedLogVolume | TRUE 73064 | USE | log(vol S), negative for hull regions |
| signed log-volume monotonicity | Mzk1SignedLogVolumeCor312Actual: signedLogVolume_mono | TRUE | USE | exactly the inclusion direction needed |
| qRegion subset hull + positive q volume | Mzk1SignedLogVolumeCor312Actual: XiEContainment | TRUE | USE | concrete structure for xi-e containment |
| containment -> signed inequality | Mzk1SignedLogVolumeCor312Actual: xi_f_signed_direction, signed_cor312_inequality | TRUE | USE | exactly signedR(q) <= signedR(theta) |
| ENNReal signed log volume | Mzk1SignedLogVolumeLemmasActual: signedLogVolume, signedLogVolume_mono, signedLogVolume_nonpos | TRUE 24744 | USE | measure-based variant |
| global theta-pilot scalar | GlobalThetaPilotLogVolumeActual: baseQReal, thetaValueFromQ, globalThetaPilotLogVolume | TRUE 190152 | ADAPT | definitions of theta/q scalars |
| older signed log volume | Mzk1SignedLogVolumeActual | NO olean | GAP | do not use until compiled |

Conclusion: do NOT write a new SignedLogVolume file. Use
Mzk1SignedLogVolumeCor312Actual/XiEContainment/signedLogVolume_mono for the signed
containment direction, and Mzk1SignedLogVolumeLemmasActual for the ENNReal version.

## 3. Log-volume monotonicity/additivity for region inclusion

| need | existing file:theorem | olean | status | use |
|---|---|---|---|---|
| Haar log-volume monotone under subset | LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceIQHullInterface.lean:68 haarLogVolume_mono | TRUE 378792 | USE | Mathlib-level; handles top case |
| region carrier logVolume_mono field | LeanFormal/IUT/IUTIII/Theorem311/QRegionCarrierInterface.lean:83 logVolume_mono | TRUE 125328 | USE | interface; qRegionCarrierSpec_logShell_volume_le_region |
| signed monotonicity | Mzk1SignedLogVolumeCor312Actual: signedLogVolume_mono | TRUE | USE | log monotone |
| source set volume monotone | LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceIQHullSignedLogVolume etc. | TRUE 95296 | ADAPT | source-set-volume variant; check exact type |
| lana componentVol monotone | Iut/Concrete/LocalConstruct/Volume.lean: componentVol_le_of_subset/componentVol_mono | NO olean (lana root) | GAP | copy/port required |
| transport signed monotone | Mzk1LogVolumeMonotoneActual: signed_le_signed_of_le_mul, transport_preserves_corollary312Inequality | TRUE 88288 | ADAPT | transport-level, not measure monotone |
| local measure monotone files | FinitePlaceNormalizedUnitScalingLogVolume.lean, FinitePlaceIQHullSharpUpperBound.lean | TRUE | ADAPT | measure_mono usage patterns |

Conclusion: for QRegionInclusion use haarLogVolume_mono and the
QRegionCarrierInterface logVolume_mono field; do not prove a new generic
monotonicity lemma. The signed wrapper already exists.

## 4. CTheta/CThetaPaper/hscalar bridges

| need | existing file:theorem | olean | status | use |
|---|---|---|---|---|
| paper CTheta definition | S2691ExactQNormalizationActual: CTheta, CTheta_def_eq | TRUE 1380520 | USE | paper scale |
| CThetaPaper definition | S2715CThetaPaperScaleActual: CThetaPaper, CThetaPaper_def_eq | TRUE 396992 | ADAPT | current hscalar uses this scale |
| exact scale relation | S2715: CThetaPaper_eq_S2691CTheta_scale | TRUE | USE | CThetaPaper=(CTheta+1)/A^2-1 |
| lower-bound consumer | S2714CThetaUpperInventoryActual: S2714_cThetaLowerBound_of_upper | TRUE 18496 | USE | upper + -A<=theta => -1<=C |
| CThetaPaper >= -1 iff bracket | S2715: CThetaPaper_ge_neg_one_iff | TRUE | USE | exact 12/10 bracket |
| CTheta >= -1 iff bracket | S2691: CTheta_ge_neg_one_iff | TRUE | USE | exact 12/10 bracket |
| CTheta >= -1 => 1/6 bound | S2691: CTheta_ge_neg_one_implies_log_bound(_source) | TRUE | USE | one-way final bound |
| upperGap iff negative C3 volume | S2807SG3aActual: S2807_upperGap_iff_neg_tensorLogVolume | TRUE 68800 | USE | identifies UpperGap with -actualC3Log... <= CThetaPaper*A |
| upperGap from packet log volume | S2807SG3bScalarActual: S2807_upperGap_of_packetLogVolume_le | TRUE? | ADAPT | needs hpacket+hscalar inputs |
| scalar iff CTheta | S2819ScalarBracketActual: S2819_scalar_iff_CTheta_ge, S2819_scalar_iff_bracket_of_packet_eq | TRUE 45640 | USE | exact CThetaPaper scale equivalences |
| hscalar target | S3025ActualThetaUpperAudit: S3025MissingThetaUpperScalar | TRUE? | GAP | Prop only, no inhabitant |
| hscalar equivalence | S3034PacketScalarBoundActual: S3034Hscalar, S3034_hscalar_iff | TRUE | GAP | Prop target only |
| our retarget comparison | Mzk1CThetaRetargetActual (new source) | NO olean | GAP-PENDING | CThetaPaper*A <= CTheta*A under 1<=A,0<=B; hand watchdog |
| conditional CTheta consumer | Mzk1Cor312FinalCThetaActual: final_cTheta_ge_neg_one | TRUE 52776 | ADAPT | conditional on PaperKummerReading/hqneg; not the hscalar target |
| numeric CTheta consumer | Mzk1CThetaConsumerIndependentActual: numericCTheta... | TRUE 84560 | GAP | model numeric, not paper |

Conclusion: existing S2691/S2714/S2715/S2807/S2819 cover definitions, scale relation,
lower-bound consumer and bracket equivalences. No CTheta*A upper is proved; hscalar
is only a Prop. Use S2715 relation and S2714 for lower bound; the retarget file is the
only new piece and is pending compile.

## 5. N5 / rhs lower bound / variant attempts

| need | existing file:theorem | olean | status | use |
|---|---|---|---|---|
| volume upper V<=stepV | Mzk1VolumeUpperActual: volumeUpper_of_stepV_identification/rhs/global | TRUE 202504 | ADAPT | upper only; wrong direction for M>=0 |
| V<=stepV inequality dictionary | Mzk1VolumeUpperLeActual: VolumeUpperLeDictionary, volume_upper_of_le_dictionary, volume_upper_le_of_rho | TRUE 174992 | ADAPT | volume upper arithmetic, not rhs lower |
| StepV alignment rows | Mzk1VStepVAlignmentActual: vStepVRows | TRUE 32208 | GAP | ledger only, no theorem |
| hull log-volume formula | Mzk1HullLogVolumeFormulaActual: productHaar_hull_log, normalizedLog_hull_eq_sum_diff, s1902LogVolume_hull_eq_normalized | TRUE 243816 | ADAPT | formula/dictionary, not R lower |
| SSIneq explicit form | Mzk1SSIneqExplicitFormActual: SSIneqExplicit, ssIneqExplicit_iff_kappa, ssIneq_of_sigma_bound | TRUE 164936 | ADAPT | explicit SS forms; no proof of input |
| SSIneq volume interface | Mzk1SSIneqVolumeActual: LgpLawInterface, SSIneqForm, wallNumeric_iff_ssIneqForm, ssIneq_iff_volume | TRUE 154592 | ADAPT | interface, needs LgpLaw input |
| CTheta final consumer | Mzk1Cor312FinalCThetaActual: final_cTheta_ge_neg_one | TRUE 52776 | ADAPT | conditional |
| CTheta/ABC combined | Mzk1E5CThetaABCActual/V4 | NO olean (some) | GAP | source only; conditional consumers |
| A490 wall alignment | A490WallThetaShiftAlignmentActual | check | ADAPT | sFactor/absLogQ relation, not lower bound |
| S3014-S3050 stack | S3014/S3029/S3050 etc | TRUE | ADAPT | exact algebra; missing actual volume/R bridge (N5-ASSEMBLY-INVENTORY) |

Conclusion: all existing N5-adjacent assets give upper bounds, explicit forms or
conditional interfaces. No existing theorem proves rhs >= -A or M >= 0. The closest
reusable exact pieces are S3029 per-label decomposition, S3050 q-expansion,
Mzk1ScalingNormalization qScaling, and Mzk1SignedLogVolumeCor312 containment; none
closes the lower-bound direction.

## 6. Region containment / Haar / measure monotonicity

| need | existing file:theorem | olean | status | use |
|---|---|---|---|---|
| generic Haar log-volume monotone | FinitePlaceIQHullInterface: haarLogVolume_mono | TRUE 378792 | USE | exact; use for measure inclusion |
| region carrier monotonicity | QRegionCarrierInterface: logVolume_mono, qRegionCarrierSpec_logShell_volume_le_region | TRUE 125328 | USE | interface-level |
| signed containment | Mzk1SignedLogVolumeCor312Actual: XiEContainment, xi_f_signed_direction | TRUE 73064 | USE | exact qRegion subset hull -> signed inequality |
| source signed log volume | FinitePlaceIQHullSignedLogVolume | TRUE 95296 | ADAPT | source-set-volume specialization |
| Haar sharp upper bound | FinitePlaceIQHullSharpUpperBound | TRUE 191712 | ADAPT | measure upper bound patterns |
| normalized unit scaling | FinitePlaceNormalizedUnitScalingLogVolume | TRUE 1266528 | ADAPT | scaling/measure monotone |
| lana componentVol_le_of_subset | Iut/Concrete/LocalConstruct/Volume.lean:205 | NO olean | GAP | needs port; not usable now |
| lana leastHull monotone | Iut/WallEquiv/Gap.lean:422 leastHull_mono | NO olean | GAP | needs port |

Conclusion: use haarLogVolume_mono + QRegionCarrierInterface + Mzk1SignedLogVolumeCor312
for the containment -> signed inequality route. Do not write new generic monotonicity.

## 7. Reuse verdict

USE directly:
- Mzk1ScalingNormalizationActual for sum j^2/qScaling/RemainingInequality;
- Mzk1ProcessionAverageActual/Mzk1ShellArithmeticIdentitiesActual for averages/sFactor;
- Mzk1SignedLogVolumeCor312Actual/XiEContainment/signedLogVolume_mono for signed direction;
- LeanFormal haarLogVolume_mono and QRegionCarrierInterface.logVolume_mono for measure
  monotonicity;
- S2691/S2714/S2715/S2807/S2819 for CTheta definitions/scale/lower-bound/bracket
  equivalences.

ADAPT, do not duplicate:
- Mzk1VolumeUpperActual/LeActual, Mzk1HullLogVolumeFormulaActual,
  Mzk1SSIneqExplicitFormActual/VolumeActual: upper/interface assets; only usable as
  inputs for upper, not lower M>=0;
- S3014/S3029/S3050 exact algebra: use, but still need actual volume/R bridge.

GAP / new work required:
- no existing rhs >= -A / M >= 0 theorem;
- no existing actual C3/theta volume to rhs bridge;
- S3019MissingBridge, S3050QUnitIdentification, paper S3029 alignment coefficients,
  S3017 hheight remain open;
- lana componentVol/leastHull monotonicity not compiled; port layer required only if
  using the lana carrier route.

Do not create new copies of:
- ScalingNormalization (exists green);
- SignedLogVolume (exists green);
- generic haarLogVolume monotonicity (exists green);
- CTheta definitions/scale relation (S2691/S2715).


## 0. A1067 tool/strong-inequality classification (mandatory)

Our target is OUR variant:
  V + gap - (sF - 1) * A >= 0, equivalently M = A - R >= 0, i.e. -A <= rhs.
This is WEAKER than lana's SSIneq:
  V - (sF - 1) * A >= 0.
Do NOT use the lana SSIneq / Wall / Thm311 / Cor312Variant / Cor312VariantHolds
as an assumption or premise. Only cherry-pick lana definitions, monotonicity
lemmas, local volume formulas and signed-log tools; rewrite any lemma whose
statement carries the strong inequality direction before using it.

Classification used below:
  TOOL = definition/monotonicity/local formula/signed-log/algebra, safe input;
  STRONG = statement is or directly encodes the stronger lana SSIneq/Wall/Thm311/
           Cor312Variant/Cor312VariantHolds; do not assume;
  GAP = no compiled object or not yet usable.

### 0.1 Section 1 (sum j^2 / sFactor / qScaling)
- sum_jsq_eq_nC_mul_sFactor: TOOL.
- qScalingNeg_eq_neg_nC_mul_sF_mul_A, qScalingNeg_div_nC: TOOL.
- RemainingInequality, M_nonneg_of_remaining: TOOL algebra; do not treat as
  lana SSIneq and do not discharge RemainingInequality by assuming SSIneq.
- avgJPlusOne/avgJSquare/sFactor/shell_average_identity/sum_sq_range/
  sFactor_eq_sL/a763_box_szpiro: TOOL.

### 0.2 Section 2 (signed log volume)
- signedLogVolume definition, signedLogVolume_mono, XiEContainment,
  xi_f_signed_direction, signed_cor312_inequality: TOOL (signed direction tool).
- signedLogVolume_nonpos / ENNReal lemmas: TOOL.
- GlobalThetaPilot scalar definitions: TOOL.
- positive_magnitude_direction_obstruction: TOOL (sign warning).

### 0.3 Section 3 (monotonicity)
- haarLogVolume_mono: TOOL.
- QRegionCarrierInterface.logVolume_mono and
  qRegionCarrierSpec_logShell_volume_le_region: TOOL (interface field; use the
  monotonicity, not a strong global inequality).
- Mzk1SignedLogVolumeCor312Actual.signedLogVolume_mono: TOOL.
- source-set-volume / sharp-upper-bound / normalized-scaling patterns: TOOL
  (adapt; they may contain upper bounds, not strong SSIneq).
- Mzk1LogVolumeMonotoneActual transport lemmas: TOOL at transport level.
- lana componentVol_le_of_subset / leastHull_mono: TOOL if ported; no olean now.

### 0.4 Section 4 (CTheta/CThetaPaper/hscalar)
- S2691.CTheta/CTheta_def_eq/CTheta_ge_neg_one_iff: TOOL (definition/algebra).
- S2691.CTheta_ge_neg_one_implies_log_bound(_source): TOOL (paper bound derived
  from CTheta >= -1; not a lana SSIneq premise).
- S2715.CThetaPaper/CThetaPaper_def_eq/CThetaPaper_eq_S2691CTheta_scale/
  CThetaPaper_ge_neg_one_iff: TOOL.
- S2715.CThetaPaper_lowerBound_of_thetaHull_upper/_paperAbsLog: TOOL (consumer
  of an upper plus ray inclusion; do not feed it SSIneq as a shortcut).
- S2714_cThetaLowerBound_of_upper: TOOL (lower-bound consumer).
- S2807_upperGap_iff_neg_tensorLogVolume / S2807_upperGap_of_packetLogVolume_le:
  TOOL definition/equivalence; the upperGap itself is an upper bound, not SSIneq.
- S2819 scalar iff lemmas: TOOL.
- S3025MissingThetaUpperScalar / S3034Hscalar / S3034_hscalar_iff: TOOL target
  Prop/equivalence, GAP (no inhabitant).
- Mzk1CThetaRetargetActual: TOOL conditional scale comparison, GAP-PENDING.
- Mzk1Cor312FinalCThetaActual.final_cTheta_ge_neg_one: TOOL conditional
  CTheta consumer; not our variant and not lana SSIneq.
- Mzk1CThetaConsumerIndependentActual numeric: TOOL/model only.

### 0.5 Section 5 (N5/rhs/variant attempts)
- Mzk1VolumeUpperActual volumeUpper_*: TOOL (upper bound only).
- Mzk1VolumeUpperLeActual VolumeUpperLeDictionary/volume_upper_*: TOOL (upper
  arithmetic; do not use as lower bound).
- Mzk1VStepVAlignmentActual vStepVRows: TOOL ledger only.
- Mzk1HullLogVolumeFormulaActual productHaar_hull_log etc.: TOOL local formula.
- Mzk1Cor312FinalCThetaActual final_cTheta_ge_neg_one: TOOL conditional.
- Mzk1E5CThetaABCActual/V4: TOOL consumer only; no olean / conditional.
- A490WallThetaShiftAlignmentActual: TOOL algebraic sFactor/absLogQ alignment;
  not a proof of our variant.
- S3014/S3029/S3050 exact decompositions: TOOL algebra; no strong inequality.
- S3016/S3016CTheta/S3017/S3019/S3034: TOOL interfaces/upper bounds; their
  missing bridge/height fields remain GAP; none supplies SSIneq.
- Mzk1SSIneqExplicitFormActual: STRONG. SSIneqExplicit and its instances state
  (sC - 1)*A <= V, the lana strong SSIneq direction. It is not our target and
  must not be assumed. ssIneqExplicit_iff_kappa is only an algebraic TOOL if
  used to rewrite, never as a premise for our variant.
- Mzk1SSIneqVolumeActual: STRONG. SSIneqForm, SSIneqKappa/ssIneq_iff_volume,
  wallNumeric_iff_ssIneqForm encode the lana SSIneq. LgpLawInterface and the
  iff algebra may be used as TOOL for rewriting, but not as an assumed strong
  premise.
- Mzk1SSINeqHullLowerActual / Mzk1SSIneqDirectAttackActual and any other file
  whose main target is SSIneq: STRONG; do not import their SSIneq conclusion as
  an assumption.

### 0.6 Section 6 (region containment/Haar)
- haarLogVolume_mono, QRegionCarrierInterface.logVolume_mono,
  XiEContainment, signedLogVolume_mono: TOOL.
- FinitePlaceIQHullSignedLogVolume / SharpUpperBound / NormalizedUnitScaling:
  TOOL measure monotonicity/local formulas (adapt).
- lana componentVol/leastHull monotonicity: TOOL if ported; no olean now.

### 0.7 Hard rule for all future reuse entries

Every new reuse row must carry one of TOOL / STRONG / GAP. A STRONG row may be
used only after being weakened to a statement that does not imply lana's
SSIneq/Wall/Thm311/Cor312Variant, or only through an explicitly weaker instance.
No document may present lana SSIneq as our target; our target remains
V + gap - (sF - 1) * A >= 0 (M >= 0), not V - (sF - 1) * A >= 0.


### 0.8 Exact disabled strong-inequality chain (abc §7 alignment)

The following names are STRONG and are explicitly DISABLED as assumptions for our
variant (they encode or directly prove the lana SSIneq/Wall/Thm311/Cor312 chain):
- Iut.Wall.SSIneq
- Corollary312Variant and Corollary312VariantHolds
- variant_of_ss_gap
- ss_iff_lgp_vcI
- gap_nonneg
- any theorem whose conclusion is V - (sF - 1) * A >= 0, or SSIneqForm /
  SSIneqExplicit, or Wall/Thm311/Cor312 completion from such a premise.

Allowed replacements:
- use only their algebra/rewrite content if it does not assume or conclude the
  strong inequality;
- otherwise weaken to our target V + gap - (sF - 1) * A >= 0 (M >= 0), which is
  strictly weaker than lana SSIneq;
- definitions/monotonicity/local volume/signed-log tools remain TOOL.

This list is authoritative for stepxi reuse entries and is cross-referenced with
coord/REUSE-AUDIT-ABC.md section 7.
