# N5-ASSEMBLY-INVENTORY — S3014-S3050 stack and M=A-R assembly

Status: READ-ONLY inventory, 2026-11-12. No Lean file, no compile.

**Gate 注（A1045/shehdd 审计）**：本文件所有“Olean TRUE/green”只表示源码与 olean 存在；**未过 DshDagWatchdog gate（无 trio/#print axioms/probe）**，一律 `PENDING-WATCHDOG`，不得写成 green gate。
Scope: tmp/sheaf/xif/paper/S3014*, S3016*, S3017*, S3019*, S3029*,
S3034*, S3050* (not S3050ConnectedSite, which is geometric and separate).
`Olean TRUE`（≠ gate）for all files below; all are **PENDING-WATCHDOG**.

## 1. Files, key signatures, dependencies

### S3014StepVProcessionAverageActual
- S3014PerLabelBound places tuple istar jValue exceptional l label
  = (-(stepVLambda p label jValue l) +
      (sum_i localNormOrder p (arithmeticTupleLocalDifferent places tuple i)) + 1)
      * log p
    + sum_{i in exceptional} (3 + log(logShellRamificationExponent ...)).
- S3014ProcessionAverageBound ... n := (1/n) * sum_{label in Icc 1 n}
  S3014PerLabelBound ....
- S3014_processionAverage_le (h : forall label, volume label <= bound label) :
  (1/n) * sum volume <= S3014ProcessionAverageBound.
- S3014ProcessionData: volume family + per-label bound;
  S3014_processionAverage_of_data.
- Dependency: LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceStepVLambda.
- Paper step: Step (iv)-(v), procession average of per-label upper bounds.

### S3016StepVQPilotIdentificationActual
- S3016StepVQPilot a b c := S2736QPilotLineBundleLogVolume (S2752J ... a b c).
- S3016WeightedGlobalQPilot T := nativeGlobalQPilotNormalizedLogMagnitude T.
- S3016IdentificationTarget a b c := S3016StepVQPilot a b c =
  S3016WeightedGlobalQPilot T.
- S3016_identificationTarget_iff is rfl unfolding.
- S3016IdentificationGap is a synonym for the target.
- Dependencies: NativeGlobalQPilotNormalizedLogVolume, S2736, S2752, S2771.
- Paper step: Step (v) q-pilot/global identification target; not proved.

### S3016CThetaUpperActual
- structure S3016CThetaUpperInterface T a b c:
  stepVLogMagnitude (eq S3016StepVQPilot); globalLogMagnitude (eq weighted global);
  identification : stepVLogMagnitude = globalLogMagnitude;
  thetaSigned, cthetaPaper, upper : thetaSigned <= cthetaPaper * |stepVLogMagnitude|.
- .stepV_eq_global (I) : S3016StepVQPilot = weightedGlobal.
- .upper_bound (I) : thetaSigned <= cthetaPaper * |S3016StepVQPilot|.
- Dependency: S3016, S2959HalfIQHullCThetaUpper, NativeGlobalQPilot.
- Paper step: Step (v)/CTheta upper interface; identification and upper are
  FIELDS of the interface, not theorems.

### S3017StepVUpperGapAssembly
- S3017_processionAverage_bound / _expanded: restatement of S3014 average bound
  for S3014ProcessionData; marked PARTIAL.
- S3017_CTheta_upper_of_height (n, hn, hheight, a b c, habc) :
  logHeight1(abcJInvariant a b c) <= S3015FinalBound n a b c,
  where hheight is the exact height-to-procession inequality.
- Dependency: S3014, S3015FinalRealInequality.
- Paper step: Step (v)-(vi); the height premise is not proved.

### S3019StepVQPilotIdentificationProofActual
- S3019_target_iff_log_sum : S3016IdentificationTarget T a b c <->
  Real.log(absNorm(qPilotLineBundleExtended ...)) =
    sum_b nativeBadLocalWeight T b * baseQLogMagnitude T b.
- S3019_identificationTarget_iff_sum : target <->
  S2736QPilotLineBundleLogVolume ... = weighted native sum.
- S3019MissingBridge : Prop :=
  forall (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))] (a b c : Nat),
    S3016IdentificationTarget T a b c.
- Dependencies: S3016, NativeGlobalQPilot, S2736, VbadPlaceIndexing, BaseQLogVolume.
- Exact meaning: there is NO theorem proving that the qPilot line-bundle
  log-volume at the S2752J family equals the native weighted base-Q log sum.
  LHS varies with (a,b,c); RHS depends only on T.

### S3029StepVAlignmentActual
- S3029DifferentTerm, S3029ExceptionalTerm, S3029StepVTerm.
- S3029_perLabel_decomposition (label) :
  S3014PerLabelBound ... = S3029StepVTerm ... + S3029DifferentTerm +
    log p + S3029ExceptionalTerm.
- structure S3029AlignmentData ... D Q S T with fields cD,cQ,cS,cT,c0,sS,sT,
  qCoeff,labelRest, and exact equalities for different/exceptional/stepV terms.
- S3029_perLabel_affine : under AlignmentData,
  S3014PerLabelBound = cD*D + (qCoeff label+cQ)*Q + (cS+sS)*S +
    (cT+sT)*T + (c0+log p) + labelRest label.
- Dependencies: S3014, S2921HeightBridge.
- Exact algebra, but AlignmentData is data (not constructed with paper coefficients).

### S3034PacketScalarBoundActual
- S3034Hscalar R ... D logQ a b c :=
  S3025MissingThetaUpperScalar ... 0 DFpd (FFpd a b c) 0 0.
- S3034_hscalar_iff : S3034Hscalar <->
  -actualC3LogShellTensorLogVolume C3 <=
    CThetaPaper fiveLabel logQ 0 DFpd (FFpd a b c) 0 0 * paperQAbsLog fiveLabel logQ.
- Dependencies: S3025, S2990, S2957 and actual C3/CThetaPaper files.
- Paper step: Step (xi) packet scalar/CTheta comparison; the proposition is
  equivalent to the displayed scalar inequality, not proved.

### S3034StepVAlignmentWitnessActual
- S3034AlignmentData : S3029AlignmentData with cD=1, cS=1, all other coefficients 0,
  D=DifferentTerm, S=ExceptionalTerm, qCoeff=0, labelRest=StepVTerm.
- S3034_perLabel_affine : affine form for this trivial witness.
- Dependency: S3029.
- Status: proves alignment structure is INHABITED, not paper numerical
  alignment. The docstring says exactly that.

### S3050StepVQExpansionActual
- S3050Unit := -((-localNormOrder p jValue)/(2*l)) * log p.
- S3050_stepVTerm_eq_label_sq_mul_unit : StepVTerm = label^2 * S3050Unit.
- S3050QCoeff label := label^2; S3050LabelRest Q label := label^2*(Unit-Q).
- S3050_stepVTerm_eq_qCoeff_mul_Q_add_rest : exact affine decomposition.
- S3050QUnitIdentification Q : Prop := exists c, S3050Unit = c*Q.
- Dependency: S3029.
- Exact algebra; S3050QUnitIdentification is an open identification target.

## 2. What can be used in N5 assembly

N5 target shape: M = A - R >= 0, and connections:
  variant: -A <= rhs (R = -rhs);
  gap: gap = rhs + sFactor(nC)*A - V(hull VC);
  box/deficit: S3014/S3029 per-label bounds and S3034 packet scalar bound.

Usable exact algebra:
- S3014_processionAverage_le / _of_data: if an actual volume family is shown to
  satisfy the per-label S3014 bound, then its procession average is bounded by
  S3014ProcessionAverageBound. Currently volume is an arbitrary input; no
  theorem identifies it with the actual theta-hull component volume.
- S3029_perLabel_decomposition / _affine: exact split of the StepV bound into
  StepV term + different + log p + exceptional, and exact affine form when
  S3029AlignmentData is supplied. Directly usable for N5 algebra.
- S3050 q-expansion: exact label^2 * Unit decomposition and affine form in an
  arbitrary Q; useful for aligning q-scaling to Q, but S3050QUnitIdentification
  is not proved.
- S3019_target_iff_log_sum / _iff_sum: exact reduction of the q-pilot
  identification target to the log/absNorm vs weighted base-Q sum equality.
- S3034_hscalar_iff: exact equivalence of S3034 scalar target to actual C3
  log-volume/CThetaPaper inequality.

Conditional/interface blocks:
- S3016CThetaUpperInterface.identification and .upper are FIELDS; the interface
  assumes the q-pilot/global identification and the CTheta upper.
- S3017_CTheta_upper_of_height is conditional on hheight.
- S3029AlignmentData is data; S3034AlignmentData is only trivial coefficients,
  not paper numerical alignment.
- S3034Hscalar is a Prop equivalent to the scalar inequality; no inhabitant.
- S3016IdentificationTarget is not proved.

## 3. Minimal lemma set for an N5 Lean theorem

1. Actual volume-to-S3014 bridge:
   forall label, actualThetaHullComponentVolume label = (or <=)
     S3014PerLabelBound ....
   MISSING: S3014 volume is arbitrary; no theorem connects it to
   rhsData/componentVol.
2. S3019MissingBridge (or direct proof):
   forall T [Fintype] (a b c), S3016IdentificationTarget T a b c.
   MISSING; no inhabitant.
3. q-pilot/CTheta upper: instantiate S3016CThetaUpperInterface (or prove
   identification/upper from 2 and CThetaPaper). Currently interface fields assumed.
4. S3017 height-to-procession inequality hheight:
   forall a b c, IsABCTriple a b c ->
     logHeight1(abcJInvariant a b c) <= (1/n) sum_j collectionBound ... .
   MISSING as a theorem (S3017 assumes it).
5. S3029AlignmentData with PAPER coefficients:
   cD,cQ,cS,cT,c0,sS,sT,qCoeff,labelRest matching actual different/exceptional/
   StepV terms. S3034AlignmentData only gives trivial cD=cS=1; paper numerical
   alignment missing.
6. S3050QUnitIdentification Q: exists c, S3050Unit = c*Q (or proved exact c).
   MISSING; needed to turn label^2*Unit into label^2*c*Q and match sFactor/A.
7. Algebraic assembly:
   variant_iff_le_rhs and gap_eq_rhs_add translate V+gap/box/deficit into
   M=A-R; these are identities, available.
8. Actual R/A identification:
   A = qPilot.absLogQ and R = -rhs must be tied to the StepV/volume bounds;
   otherwise N5 only proves an abstract arithmetic statement.

## 4. Is N5 already present?

No. The stack contains exact arithmetic decompositions (S3014 average, S3029,
S3050), conditional interfaces (S3016 CTheta, S3017 height, S3034 scalar), one
named missing bridge (S3019MissingBridge) and one named q-unit gap
(S3050QUnitIdentification). There is no theorem connecting actual
thetaHull/componentVol to S3014 volume, and no theorem with the final M=A-R
conclusion.

The strongest usable exact blocks for N5 are S3029_perLabel_decomposition/
S3029_perLabel_affine and S3050_stepVTerm_eq_qCoeff_mul_Q_add_rest, plus the
S3019 target reduction; they supply algebra but not the actual volume/R link.

## 5. S3019MissingBridge in one line

S3019MissingBridge is exactly:
  forall T : SourceNativeInitialThetaData and a b c,
    S2736QPilotLineBundleLogVolume (S2752J fiveLabel a b c)
      = nativeGlobalQPilotNormalizedLogMagnitude T,
equivalently (S3019_target_iff_log_sum):
  forall T a b c,
    Real.log(absNorm(qPilotLineBundleExtended ...)) =
      sum_b nativeBadLocalWeight T b * baseQLogMagnitude T b.
It is a Prop with no proof; LHS depends on (a,b,c), RHS only on T. No existing
theorem in S3019 or its imports proves it.

No Lean file written; no compile claimed.
