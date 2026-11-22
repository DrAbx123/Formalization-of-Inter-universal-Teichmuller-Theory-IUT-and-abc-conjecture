# Xi-f paper task ledger (maintained)

Last updated from current files. Statuses:
* ACTUAL: compiled actual (integration verification still required).
* CONDITIONAL: compiled with explicit hypotheses/parameters.
* EXACT: precise missing proposition/object, no inhabitant.
* INVALID/SUPERSEDED: do not use or extend.

## Canonical consumer chain

  PaperXiFSourceLink
    source_identifications
    qPilotLogVolume_eq_paper
    link_identification
    link_implies_inclusion
  -> PaperXiFInclusion
  -> PaperSignedHull / paperCertificate
  -> StepXIContract -> Cor312Conclusion

## ACTUAL reusable

* QPilot side
  - PaperQPilotObjectActual, PaperQPilotLogVolume
  - ConcreteQPilotLogIdentificationActual: qPilotLogVolume_eq_paper conditional on
    ConcreteSourceQIdentification.
  - PaperQParameter/localSignedLog definitions.
* Root/normalization
  - QVFamRootFactorCorrectionActual (q[2u] coefficient = order/(2l))
  - RootCorrectedQPilotScalarActual (root scalar = classical/(2l))
  - S638PaperThetaNormalizationActual (root power; classical = 2l * paper)
  - TwoLthRootKummerActual (hodgeTwoLthRoot^(2l)=qVAlgClosedUnit)
* Signed hull
  - S657RootSignedHullIndependentActual (positive magnitude procession;
    average_nonneg; no S645)
  - S658RootNormalizedPaperSignedHullActual (PaperSignedHull with A/hnormal params)
  - PaperSignedHullSignedActual (classical C3 signed hull, conditional hlog/hnormal)
* Extension root hull
  - PaperRootExtensionProductHaarActual (product Haar on L_b product)
  - PaperRootExtensionNormBoundActual (norm bound from RootQUnitNormLeOne)
  - PaperRootExtensionThetaHullAuditActual (image hull, Haar, imageHullLog)
  - PaperRootExtensionFieldScalingHaarActual (field-scaled hull/log)
  - PaperRootExtensionThetaHullActual (full unit-ball hull, log 0)
* Root stack
  - S356RootStackActionGroupoidActual (roots + mu_2l groupoid)
  - S392RootStackSectionMonoidActual (candidate section monoid)
  - S824RootStackyHaarVolumeActual (W1, EXIT=0, axioms propext/choice/Quot.sound):
    actual mu_2l Haar invariance via finite-order distribHaarChar; stacky log
    volume = log dHC on L(mu_2l); actual q[2u] identity
    log V(root ball) = (1/(2l)) log V(q ball); branch independence; dichotomy
    stacky log = least-hull log <=> c_norm = order (under the named
    StackCharacterNormComparison).  Memo: W1_STACKY_HAAR_MEMO.md.
* Contract/model
  - PaperLevelXiFTargetProofActual.globalQPilotLog_le_globalThetaHullLog
    (actual model inequality; no downstream paper bridge)
  - S650ActualSignedCor312Contract (finite/model signed contract)
  - S653RootThetaTensorHullCarrierGapActual (tensor gap filled except
    RootThetaRootNormBound, which is actual from RootQUnitNormLeOne)

## CONDITIONAL actual

* S646PaperRootHullComparisonActual
  qPilotClassicalLog <= paperRootThetaHullLog
  given PaperRootCoefficientLeRootNorm, Haar pos, hull finite.
* S640RootHullGapComparisonActual: qPilotClassicalLog <= halfRootThetaHullLog
  (c_norm/(2l) model), conditional hpos/hfin; PaperRootHullFormulaGap
  (paper order/(2l)) remains exact and completion-impossible.
* S676FinalConditionalCor312Actual: S669 source link -> PaperXiFInput ->
  paperCertificate -> Cor312Conclusion, conditional on q/source/link + finite links.
* S669S663PaperXiFSourceLinkActual: theta side uses S663 actual PaperSignedHull
  (A/hnormal discharged); conditional PaperXiFSourceLink/PaperXiFInclusion
  with explicit q/source/link fields.
* S665PaperSignedHullXiFInterfaceActual: PaperSignedHull fields actual (given
  A/hnormal); conditional PaperXiFSourceLink constructor. Exact q/link fields.
* S668QPilotRootExtensionPerBActual: actual per-b map qPilot block ->
  rootNormedExtension via S312/blockLinearEquiv; exact per-b containment.
* S666QPilotRootExtensionInterfaceActual: qPilot region/log + extension image hull/log
  actual; containment/log comparison explicit Prop (no actual map).
* S649RootThetaExtensionComparisonActual
  extension comparison + completion map as explicit data.
* S650RootThetaXiFThetaSideActual
  theta-side PaperXiFSourceLink constructor from bridge fields.
* S658RootNormalizedPaperSignedHullActual
  PaperSignedHull from root magnitude procession + A + hnormal.
* S634PaperXiFConditionalCor312Actual
  final conditional package from hq/hgap/source/links.
* S656RootThetaXiF/... sign audit: use S657/S658, not S642/S644/S645.

## EXACT missing (canonical)

* ConcreteSourceQIdentification:
    sourceQPilotSignedLog = localSignedLog C3.q.
* RootQUnitNormLeOne: DONE actual (S664RootQUnitNormLeOneActual).
  => RootExtensionProductNormBound actual; no hypothesis.
* qPilot -> product hull comparison/containment on RootExtensionProductCarrier.
* Paper hull equality: rootExtensionProductImageHull = paper holomorphic/lambda-O hull
  (or actual log/measure equality).
* PaperXiFSourceLink fields: source_identifications, qPilotLogVolume_eq_paper,
  link_identification, link_implies_inclusion. Theta side now actual via S669;
  these four are the only explicit params.
* Paper StepXIContract fields (paper qSigned/thetaSigned/targetSigned/ipl/she/apt).

## EXACT but completed/obsolete (do not chase)

* PaperRootHullFormulaGap (completion carrier): impossible by S342 completion root;
  obsolete carrier. Do not fill.
* RootThetaProductHaarGap on full algebraic-closure product: no Haar on full AC;
  use PaperRootExtensionProductHaarActual instead.
* RootThetaToCompletionHullMapGap: only needed if completion surrogate is used.

## INVALID/SUPERSEDED

* S679DirectScalarComparisonActual: INVALID general route. Correct paper
  average uses l* positive classes weight 1/l* (S694); coefficient (l+1)/24
  still >1 at l=29, and S679 uses per-b qPilot instead of global V_bad
  procession-normalized qPilot. Use global comparison only.
* S694ThetaAverageNormalizationActual: actual paper label average
  (l* classes, weight 1/l*, theta exponent j^2/(2l)); per-b scalar route
  invalid, need global V_bad comparison.

* ConcreteSourceComparisonObstacle: generic statement false at zero bad-q; NOT
  paper target. Do not use/prove its scalar inequality.
* PaperCompletionThetaValueActual: invalid completion 2l-root.
* BadPlaceHalfRootSupplyActual.HalfRootInCompletion: invalid completion root.
* S642/S643/S644 root processions: sign/normalization stale, not compiled;
  superseded by S657/S658.
* S645RootNormalizedPaperSignedHullActual: negative signed procession;
  haverage unsatisfiable; superseded by S657/S658.
* S654RootSignedHullSignCorrectionActual: now a thin alias wrapper of S657
  (EXIT=0); no new content. Use S657 directly.
* S641/PaperLevelXiFTarget*: actual scalar model but no PaperXiFInclusion/Cor312
  downstream bridge; do not treat as final paper proof.

## PENDING tasks

* S659: rebuild RootNormalizedThetaHullActual after fixing
  GlobalQVFamThetaHullScalarActual (measurable instances, named args).
* S660: duplicate wrapper of S657/S658; compiles but adds no new content. Use S657/S658.
* S661: done. S654 is now alias of S657; S645 retired/uncompiled.
* S662/S663: DONE. S663ActualAverageNormalizedHaarActual builds actual
  arbitrary-average normalized Haar + IQHullLogVolumeInterface + hnormal,
  and instantiates S658 with A/hnormal discharged (only places/tuple/nu inputs).
* Discharge RootQUnitNormLeOne from qVFamily q norm < 1.
* Build qPilot -> RootExtensionProductCarrier containment/log comparison.
* Add paper hull equality bridge (rootExtensionProductImageHull vs paper lambda-O).
* Fill PaperXiFSourceLink q/link fields.
* W1/S824: stacky 1/(2l) normalization is now an actual Haar theorem on the
  finite root stack, but "least hull log = stacky volume" is equivalent to
  S736 `c_norm = order` (kernel-checked dichotomy).  Remaining exact inputs:
  StackCharacterNormComparison (Haar determinant = spectral norm power) and
  the completion scaling data D for the least hull itself.

## Notes

* PAPER_THETA_NORMALIZATION_STATUS.md
* PAPER_EXTENSION_HULL_STATUS.md
* FIVE_PAPER_GAPS_STATUS.md
* PAPER_OBJECT_AUDIT_EXTENSION.md
* NOTATION_Q_UNDERLINES.md / Q_SYMBOL_AUDIT.md
## 2026-10-30 — S1069: S1051/S1055 INVALID AS PAPER (wrong qPilot object)

* **S1051PaperGlobalFinalActual** and **S1055** are INVALID AS PAPER.
  Their "paper global qPilot" is built from qPilotPaperRegion, which is the
  theta j=1 region at paperRootCoefficientFamily cRoot = order/(2l), not the
  qPilot normalized region at c_norm = order.
* S1065 proves the exact failure: paperRootThetaHullNonzero = qPilotPaperRegion,
  hence qPilotPaperRegion = theta hull (q = theta).  A qPilot equal to the theta
  hull cannot be the paper qPilot.
* Do not use S1051/S1055 as paper; do not chase S1051PaperQParameterCard or the
  S1054 links built on that certificate.
* **Correct route: S1062-S1068.**
  - S1062: classical qPilot region F(c_norm) ⊆ nonzero paper root theta hull.
  - S1064: weighted global from per-b classical qPilot <= theta nonzero;
    S1063 is absent, per-b inequality remains exact.
  - S1065: audit of the old path (INVALID AS PAPER).
  - S1066: absent.
  - S1067: coefficient audit: qVFamNormalizedCoefficient = order rfl;
    paperRootCoefficientFamily = order/(2l) rfl; qPilotClassicalRegion uses
    c_norm; the Supply c_norm = order identification is an exact gap.
  - S1068: corrected signed target globalQPilotLog <= globalThetaHullLog
    (actual), per-b qPilot <= theta hull (actual).
* Exact remaining on the correct route: S1063 per-b classical qPilot <= theta
  hull (if no file), S1064 global weighted, S1068 signed target; plus the
  separate finite-carrier/link checklist (S994FiniteInput actual; source link /
  finite links exact).


## 2026-10-30 — S1096: qPilot q[1u] log formula supply

* NormalizedGeneratorSupplyMissing remains EXACT, not fabricated.
* It is reduced to the exact coefficient gap
  qVFamNormalizedCoefficient = qVFamPureCoefficient (S1096CoefficientGap).
  Under that gap the actual qVFamily generator in CommonPrimeCompletion is a
  NormalizedGeneratorSupply at qVFamPureCoefficient, so qPilotQ1URegion_logVolume
  and the negative magnitude formula are actual conditional.
* Do not claim the default valuation norm equals the normalized spectral norm.
  Coefficient audit: qVFamDefaultCoefficient = order * log_p(residueNormBase)
  (= order * f), while the normalized coefficient is c_norm = order/e under the
  normalized norm formula.  The gap therefore needs the (unproved) relation
  between f and e; it is not automatic and is not assumed.
* Exact minimal input: S1096CoefficientGap (= QVFamNormalizedCoefficientGap).
  Without it, NormalizedGeneratorSupplyMissing and the q[1u] log formula stay
  exact.


## 2026-10-30 — S1107: canonical qPilot log / qParameter card / source link

* canonicalQPilotLog is filled by the S1091 actual qVFam Haar log on
  qPilotQ1URegion (arithmeticTupleNormalizedLogVolume with Measure.addHaar).
* Closed formula is actual conditional on S1096CoefficientGap
  (qVFamNormalizedCoefficient = qVFamPureCoefficient); unconditional formula is
  still exact.
* qParameter card: qParameter = exp(canonicalQPilotLog), positivity automatic;
  log-nonvanishing requires the exact sign field canonicalQPilotLog ≠ 0
  (S1107CanonicalLogNonzero).  No unconditional sign/card.
* Source link / link identification / finite links remain exact fields; the
  checklist constructor uses the actual canonical log and card under the sign.
* Exact list: S1096CoefficientGap + canonical-log nonzero + source link +
  link identification + finite links.


## 2026-10-30 — S1115: E character/norm audit

No actual proof of the E character/norm formula exists.  S885 packages the
uniformizer/unit-factor/uniformizer-factor/factor-norm data as exact input and
its last field is the factor-norm target itself (circular if used as a proof);
S892 reduces the general norm formula to RootStackCharacterNormComparisonAtDQp;
S897/S903 reduce the E comparison to RootStackHaarFactorNormPow dQpFactor.
Remaining exact items: DVR uniformizer datum, unit-factor-one identity,
uniformizer-factor identity, factor-norm formula.  See
tmp/sheaf/xif/paper/S1115ECharacterNormAudit.md.


## 2026-10-30 — S1121: NormedAlgebra L -> ambient / NontriviallyNormedField E

* Search first: S893 only records the exact missing instances; S912 provides
  NormedAlgebra (rootNormedExtension) (rootStackExtension), not
  NormedAlgebra (rootNormedExtension) (rootNormedAmbient).  S1116 needs the
  ambient instance for its DVR argument (NontriviallyNormedField E).
* Mathlib actual reusable instance:
  Mathlib.Analysis.Normed.Algebra.Basic:353
  (F : IntermediateField K L) [NontriviallyNormedField K] [NormedField L]
  [NormedAlgebra K L] : NontriviallyNormedField F.
* New S1121 file supplies the missing NormedAlgebra L ambient instance (subtype
  inclusion; norm_mul) and then infers NormedField/NontriviallyNormedField E.
  It does not duplicate S912: S912's target is L -> E, S1121's is L -> ambient.
* EXIT=0, appended to compile queue.


## 2026-10-30 — S1159: SourceRun C m shape

SourceRun actual fields: carrier C, W.1 autom, W.4 ind2Data, AlgorithmInput
(source/route/source_image_nonempty), output := runAlgorithm, presentation :=
sourcePresentationOfCarrier, algorithm := sourceAlgorithmOfCarrier, forgetRun
:= output.target.  All equalities are rfl; routeTrace is constructible auxiliary.
Exact first gap: stripOfChoice/stripOfRun/diagramOfRun and the operation-arrow
realization with commEnv square; no Choice -> SourceFTimesMuPrimeStrip map exists
(card routes (a)(b)(c) blocked).  Forbidden: Q<=H/q membership, compatible:Prop,
arbitrary strip choice, renamed generic fLinkAt/canonicalLift, pre-existing
commEnv.  Report: coord/reports/S1159SourceRunShape.md.


## 2026-10-30 — S1177/S1180: SourceOutputPrimeStripInterpretation exact first gap

No actual construction.  Actual reusable: fPrimeStripAt/fLinkAt, AlgorithmInput/
runAlgorithm, routeTrace endpoint theorem.  Exact first gap: SourceEvaluationUnitPortion
G upper lower for actual non-self strips; reduced to SourceTimesMuKummerLayer via
SourceEvaluationUnitPortion.ofKummerLayer.  Only gate inhabitant
sourceEvaluationArrow_self exists (trivial, not paper evaluation).  Local
timesMuEvaluationComparison actual but no FPrimeStrip.Mon v -> local monoid bridge.
No new weak Lean wrapper written.  Report:
coord/reports/s1177-source-output-prime-strip-exact-gap.md.


## 2026-10-30 — S1229: SourceProcessionBoundary audit

SourceProcessionBoundary does NOT construct Core/Profile; Input.carrier is a
field supplied by the caller. concreteInput uses the concrete finite model, not
arbitrary I.family.index; no source_index connection. Minimal actual path:
S1221 stripOfChoice/linkOfChoice + S1225 index permutations/ind1/2/3, then Core
laws (permutation identities, not yet proved), then Profile S1225LogVolumeShiftLaws
(exact first source field), then Carrier/AlgorithmInput/SourceRun.  No new Lean
wrapper written. Report: coord/reports/s1229-source-procession-boundary-audit.md.


## 2026-10-30 - S1294: S1262/S1275/S1287 consumer audit

S1262 HDD lattice, S1275 SHE localization/readout_ref, S1287 actual consumer
assembly all EXIT=0; axioms only propext/Classical.choice/Quot.sound; no sorry.
S1287 is actual SourceHDDReadout-field assembly. Full SourceSHEHDDCompatibility
still exact at localizeSection + localize_hdd_compat; S1275 defines the exact
type but no section map. Report: coord/reports/s1294-hdd-she-consumer-audit.md.

## 2026-10-30 - S1301: original vs simplified audit

Audited new products. Marked SIMPLIFIED/NOT-FINAL: S1195 upperEnv graph/fLinkAt,
S1234 finiteKernelRun, S1262/S1286/S1287/S1295 rank-one unit-section HDD,
S1270 IQSpan/Q-vector capsule, S1282 level=toNat, S1219 concrete one-place
tensor, S1225-S1231 Core level:=0, S1188 generic fLinkAt Kummer layer,
S1168/S1164 candidate squares. Actual reusable components only: S1221
stripOfChoice/linkOfChoice, S1232 sourceLogVolume laws, S1233 thetaPossibleImage,
S1190 fixed-subgroup algebra, S1170 routeTrace. S1283 absent; algebraic-closure
roots are not completion roots. Full paper objects D5-D11, actual integral
log-shell/polyIso, nontrivial kappa, C3 completion roots, genuine HDD hull+det,
theta line bundle remain missing. Report:
coord/reports/s1301-original-vs-simplified-audit.md.

## 2026-10-31 — S1453: Route A S1413 recheck/report

S1413SourceKPlaceQComparisonActual remains unbuilt: lake env lean EXIT=-1, no
olean. Source-level sectionKPlace/sectionQ/order/valuation/norm declarations are
present but kernel-unverified; do not import. S605 KSideQVComparisonData exact
first fields: qVFamilyKLift = kSidePlace; S1413ShadowEqualsNative; sectionQ =
qVFamilyK; K-side TateCurveComparison. No Lean bridge written. Report:
coord/reports/s1453-route-a-s1413-report.md.
