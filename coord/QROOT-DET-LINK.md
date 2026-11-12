# QROOT-DET-LINK — GAP-DET-QROOT audit (A1056)

Status: read-only; no compile.  Goal: existing identification between the det
unit / `S1422.detDataOfHull` unit and `qroot^{j²}` / `scaleElt`.

## 1. Exact definitions in the requested files

### `S3050StepVQExpansionActual.lean`
- `S3050Unit p jValue l : Real :=`
  `-((-localNormOrder p jValue) / (2 * l : Nat)) * Real.log (p : Real)` (`:18`).
  It is a **scalar** log-magnitude, not a unit; `jValue` is a completion element.
- `S3050_stepVTerm_eq_label_sq_mul_unit` (`:30`):
  `S3029StepVTerm ... label = (label : Real)^2 * S3050Unit p jValue l`.
- `S3050QCoeff label = (label : Real)^2` (`:37`).
- `S3050LabelRest Q label = (label)^2 * (S3050Unit - Q)` (`:42`).
- `S3050QUnitIdentification Q : Prop := ∃ c, S3050Unit = c * Q` (`:56`).
  This is the only 'unit ↔ Q' identification; it is a **Prop**, not proved.

### `S3016StepVQPilotIdentificationActual.lean`
- `S3016StepVQPilot a b c : Real :=`
  `S2736QPilotLineBundleLogVolume (l := S2771FiveLabel) (S2752J S2771FiveLabel a b c)` (`:30`).
- `S3016WeightedGlobalQPilot T := nativeGlobalQPilotNormalizedLogMagnitude T` (`:36`).
- `S3016IdentificationTarget a b c : Prop := S3016StepVQPilot a b c = S3016WeightedGlobalQPilot T`
  (`:41`); `S3016IdentificationGap` (`:53`).  No qroot/scaleElt.

### `S2771Gap1ClosedActual.lean`
- only `S2771FiveLabel`, `S2771W`, and
  `S2771_rankTwoTorsionBasis` (`:27`): rank-two 5-torsion basis.
  No qroot, scaleElt, det unit, or line-bundle unit.

### `S2772BridgeConditionalActual.lean` / `S2772C3NormalizedRegionLogVolumeActual.lean`
- `S2772Bridge` (`:17`) builds a `Cor312ToABCBridgeInterface` from a
  fractional-ideal unit `J` and an epsilon-comparison gap; no qroot/det unit.
- `c3NormalizedRegionLogVolumeConsumer` (`:36`) =
  `Real.log (c3NormalizedTensorHaar (C3PerPlaceUpdateRegionAll ...)).toReal`;
  a scalar region log-volume, not a det unit.

### q-pilot line bundle (`S2735QPilotLineBundleActual.lean`)
- `qPilotIdeal := gaussianFieldFivePrimePlus * gaussianFieldFivePrimeMinus *
  gaussianField2161Plus * gaussianField2161Minus` (`:23`);
- `qPilotLineBundle : SourceLineBundle` (`:35`);
- `qPilotLineBundleExtended J := qPilotIdeal * J` (`:87`);
- `S2736QPilotLineBundleLogVolume J := Real.log (absNorm (qPilotLineBundleExtended J))`
  (`S2736...:19`).

These are **ideal/lattice line-bundle units** (fractional ideals), not the
local root unit `qroot^{j²}`.

### qroot in the theta side
`HullDetObjectActual.lean`:
- `localQrootLogVolume T b := Real.log (rootNormedElementNorm T b)` (`:78`);
- `localThetaPilotLogVolume T j b := Real.log ‖rootNormedThetaValueInL T b j‖` (`:86`);
- `localThetaPilotLogVolume_eq_gaussExponent_mul` (`:97`):
  `localThetaPilotLogVolume = (gaussExponent j : Real) * localQrootLogVolume`.
  This is a scalar log relation for the root theta values.
`BadPlacePaperConstantsActual.lean`:
- `hodgeTwoLthRoot T b ^ (gaussExponent j).toNat` (`:126`);
  qroot power as a value, not a det unit.

## 2. Is there any theorem linking det unit `G` to `qroot^{j²}` / `scaleElt`?

**No.**  Searched `S3016`, `S3050`, `S2771`, `S2772`, `S2735/2736`, `S2752`,
plus qroot/scaleElt grep across `tmp/sheaf/xif/paper`.

- `S1422.detDataOfHull` (`:262`) was not referenced in any of the files.
- `S1422.dependentDetDataOfChar` uses `dependentPrimeUnit`/
  `dependentPrimeInverseUnit` (prime-inverse diagonal units), not `qroot`.
- `scaleElt` (lana `ThetaRegion.lean:136`) is not used in these files.
- `qroot` appears only as a norm/log-volume scalar (`HullDetObjectActual`),
  or as a `hodgeTwoLthRoot` power, never as a det/tensor unit.
- `S3050Unit` is a scalar with shape `j²·ord/(2l)·log p`; it is not a group
  element and not identified with `qroot`.

## 3. Minimal new declarations

If a det-unit ↔ qroot link is needed, the minimal additions are:

1. **Root unit**
   `rootUnit (place) (qroot : Completion) : (CommonPrimeCompletion place)ˣ :=`
   `Units.mk0 qroot qroot_ne_zero`;
   and `rootUnit_pow : rootUnit ^ m = Units.mk0 (qroot^m) ...`.
2. **Det unit**
   from `S1422.detDataOfHull`/`dependentDetDataOfChar`:
   `detUnit (G : ((v : {v // v∈s}) → Completion v)ˣ)`
   (the coordinatewise prime-inverse unit), or directly
   `S1422.dependentPrimeUnit`/`dependentPrimeInverseUnit`.
3. **Local norm/order bridge**
   `localNormOrder p (qroot^m) = m * qOrder/(2l*e)`;
   the lana source has `ordp_qrootOf` (`Iut/Concrete/ThetaLocalConstruct/Data.lean:327`)
   for the L root, but not a theorem linking it to `S1422`'s det unit.
4. **Identification theorem**
   `detUnit = tensorProduct (rootUnit ...) (gaussExponent j)`
   or `detUnit = ∏_i incl_i (qroot^{j²})` (the `scaleElt` shape);
   this is the missing GAP-DET-QROOT.
5. **Log-volume corollary**
   `logVolume(detUnit • O) = - (j² * qOrder/(2l)) * log p` (matching
   `S3050Unit` or `stepVLambda`).

## 4. Verdict

- `S3016`/`S3050`/`S2771`/`S2772` contain **no qroot/scaleElt/det-unit link**.
- The q-pilot line bundle is an ideal/fractional-ideal object; qroot appears
  only as a scalar norm/log-volume or a `hodgeTwoLthRoot` power.
- `S1422.detDataOfHull`'s unit is a dependent-product prime-inverse unit, not
  identified with qroot.
- Minimal bridge: define `rootUnit` and `detUnit`, prove the tensor/diagonal
  equality, then derive the log-volume identity.  No existing theorem does this.
