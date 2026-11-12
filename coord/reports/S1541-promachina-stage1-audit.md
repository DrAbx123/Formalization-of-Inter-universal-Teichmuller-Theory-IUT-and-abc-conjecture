# S1541: promachina 1fa Stage1 四文件只读审计

Date: 2026-10-31 (Asia/Shanghai)
Snapshot: `vendor/promachina/snapshots/1fa6387f11fb6dc67eb618b8138e6bc64f56b039`
Upstream: promachina/iut-lean master `1fa6387f11fb6dc67eb618b8138e6bc64f56b039`, tree `c32abf9c5b85fb44a1815182a465d714a2706972`
Metadata: `vendor/promachina/review-1fa6387f.json`
Toolchain of snapshot: Lean `v4.30.0`, Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`.
Current project toolchain: Lean `v4.32.2`.  This audit does **not** claim that any copied declaration compiles here.

Audited files (SHA256; line counts are `read` totals):

| file | lines | SHA256 |
|---|---:|---|
| `Iut/Stage1/IUTStage1SourceCore.lean` | 40937 | `927CD99712FA5EA2E0AC0B588F7DCA0A462CE7DDA485FC508214EB552DA24C44` |
| `Iut/Stage1/IUTStage1StepXI/Core.lean` | 231633 | `24F6560859D0DEA1FA1A17DB5F85D3471847734B133BB82A744B477C0254193F` |
| `Iut/Stage1/IUTStage1ConstructedTheorem311.lean` | 874 | `1133068F40078D389ADE1FFC9AEBF30BD51F7ACD4DBE86CAE5E8D960BAE6D09C` |
| `Iut/Stage1/IUTStage1FrobenioidShift.lean` | 81839 | `115B783E4EDF9EF959DE9EB953F644DF93FA982C7D214B11B78629DAE7FC6D22` |

Status vocabulary used below (same labels as `coord/XI_F_ORIGINAL_ROUTE.md` §12):

- `[BUILT]`: a term/inhabitant exists in Lean, with a body.
- `[CONDITIONAL]`: a constructor from an explicit input X exists; X has no inhabitant.
- `[MISSING]`: only a type, Prop, structure field, or opaque label is recorded; no inhabitant.
- `[LABEL]`: inert identifier (`String`-backed), no mathematical content.

Read-only audit: only `read` / `grep` / filesystem scans were run.  No Lean build, no `#print axioms`, no comparator.  `statement_compiles`, `proof_body_checked`, `kernel_closed` are all **not run**; `target_accepted = false`.

## 0. Executive answer

1. The four files contain **no paper-level construction** of Xi/Phi/hull/log-volume, ThetaLink, ArithmeticVectorBundle, or HDD.  They contain finite "shadow" data, numeric bookkeeping, and conditional constructors.
2. **Xi/Phi**: `Phi` is canonically inhabited, but only as the finite hull-approximant type of a supplied hull shadow.  `Xi` is not inhabited in general; it needs the exact log-volume calibration `IUTStage1Remark395PossibleImageExactXiFamilySource` (SourceCore:7650).  No complex-analytic hull is constructed.
3. **hull**: there are genuine definitions with bodies: `IUTStage1Remark395HolomorphicHullSystem.phi` is the intersection of all supplied hulls (SourceCore:3196), and `IUTStage1Remark395DirectProductHullSystemSource.productHull` is a literal coordinate product (SourceCore:3487).  But the hull predicate and `logVolume` remain fields of a structure.
4. **log-volume**: the four files construct arithmetic/numeric identities (`bundleLogVolume = sum`, `determinantLogVolume = sum`, `normalizedLogVolume = tensorPower / M`, `Real.sqrt` of a normalized factor), not an analytic log-volume.  `Iut/Foundations/RegionMeasure.lean:11-13` explicitly says it "does not define IUT log-volume analytically".
5. **ThetaLink**: the only occurrence in the four files is the field assignment `thetaLink := data.realization.zeroToOneThetaLink` in `IUTIIIHorizontalCompatibility.ofM2` (ConstructedTheorem311:749).  The underlying `zeroToOneThetaLink` is a toy order equivalence of `Nat`-degree Frobenioid objects (`Foundations/ThetaHodgeTheater.lean:404,433,529,563`).  There is **no theta line bundle, theta section, theta divisor, or scheme** in the four files.
6. **ArithmeticVectorBundle**: only log-volume skeletons.  SourceCore:7852-7853 states verbatim that the record "does not construct the underlying arithmetic vector bundle".  `rank` is `Fintype.card γ` of summand labels; there is no module, lattice, localization, or integral structure.
7. **HDD**: `HDDCompositeData` still requires a `hullDetBridge` field (`Foundations/AlgorithmicBridge.lean:824-828,294-298`).  StepXI's `withHDDHullDetBridge` only rewrites that field (`StepXI/Core.lean:71086-71104`).  There is no rank-`>1` HDD local lattice in the four files or in Stage1 (grep `HDDLocalLattice` = 0).
8. **Verdict for current nodes**: promachina 1fa cannot fill the exact residuals of **S1422, S1424, S1479, or S1487**.  S1422 already has a stronger actual Haar hull log-volume; its missing `DependentProductScalingChar` is not in these four files.  S1424/S1479 need a geometric theta line bundle/section, absent everywhere in the snapshot.  S1487 needs a q-pilot scalar equality against concrete C3, also absent.
9. **Qualified exception (outside the four files)**: `Iut/Foundations/SourceTheorem311.lean:6999-7275` proves a *local* distributive-Haar-character formula `distribHaarChar (rationalPrimeUnit p) = p^{-[L:Q_p]}` from the residue quotient (`HaarDegreeFormula`, `ResidueQuotientFormula.toHaarDegreeFormula`, `normalizedHaarMeasure_rationalPrimeDilation`).  This is a plausible donor for the **character identity** in S1422 (for degree-one `Q_p` factors, after a finite-product character lemma), but it is not in the four files, has no dependent-product version, and does nothing for the rank-`>1` HDD lattice.  This route was **not** compiled or type-checked.

## 1. What is actually built in the four files

The following table separates declarations with genuine bodies from structure fields.  Line numbers are the declaration lines.

### 1.1 Hull

| declaration | file:line | body / content | dependencies |
|---|---|---|---|
| `IUTStage1Remark395HolomorphicHullOperator` | SourceCore:3006 | **structure**; fields `phi`, `isClosed`, closure laws, `logVolume`, `logVolume_mono` | Mathlib `Set`, `Real`; no inhabitant |
| `...toClosureOperator` | SourceCore:3026 | `[BUILT]` packages the fields as a Mathlib `ClosureOperator` | the structure above |
| `...transport` | SourceCore:3125 | `[BUILT]` carrier-change hull operator; `phi := e ⁻¹' data.phi (e '' region)` | `Equiv`, `Set` |
| `IUTStage1Remark395HolomorphicHullSystem` | SourceCore:3182 | **structure**; `isHull`, intersection law, `logVolume`, monotonicity | no inhabitant |
| `...phi` | SourceCore:3196 | `[BUILT]` literal intersection of all supplied hulls containing the region | `isHull` field |
| `...toHolomorphicHullOperator` | SourceCore:3260 | `[BUILT]` projects the intersection operator to the operator structure | above |
| `IUTStage1Remark395ProductHullSystemSource` | SourceCore:3314 | **structure**; product-hull family, intersection parameter, log-volume | no inhabitant |
| `IUTStage1Remark395DirectProductHullSystemSource` | SourceCore:3470 | **structure** with actual coordinate-product definitions | no inhabitant |
| `...productHull` | SourceCore:3487 | `[BUILT]` literal coordinate product of the supplied parameter sets | `Set`, dependent functions |
| `...coordinateProjection` | SourceCore:3493 | `[BUILT]` coordinate image of a region | `Set` |
| `...intersectionParameter` | SourceCore:3500 | `[BUILT]` family of coordinate projections | above |
| `...toProductHullSystemSource` | SourceCore:3558 | `[BUILT]` actual projection | above |
| `...toHolomorphicHullSystem` | SourceCore:3570 | `[BUILT]` actual projection | above |
| `IUTStage1HolomorphicHullLogVolumeShadow` | SourceCore:5988 | **structure**; `hull : ClosureOperator (Set α)`, `logVolume`, monotonicity | Mathlib `ClosureOperator`; no inhabitant |
| `...ofRemark395Operator` | SourceCore:6000 | `[BUILT]` | above |
| `...hullRegion` | SourceCore:6027 | `[BUILT]` `data.hull region` | above |
| `...toRegionHullOperator` | SourceCore:6134 | `[BUILT]` projects to `RealLineCopy.HullOperator` | promachina `Copy`, `Region`, `HullOperator` |
| `...toRegionMeasure` | SourceCore:6145 | `[BUILT]` `volume region := logVolume region.toSet` | promachina `RegionMeasure` |
| `IUTStage1HullLogVolumeApproximant` | SourceCore:6311 | **structure**; approximant set, closedness, containment, log-volume sandwich | no inhabitant |
| `...canonical` | SourceCore:6329 | `[BUILT]` approximant `:= hullRegion region`; proofs from hull laws | hull shadow |
| `IUTStage1ExactHullLogVolumeApproximant` | SourceCore:6405 | **structure**; approximant plus exact log-volume equality | no inhabitant |
| `...canonicalOfClosed` | SourceCore:6419 | `[BUILT]` only for a closed region | hull shadow + closedness |
| `IUTStage1HullLogVolumeApproximantFamily` | SourceCore:6496 | **structure**; family plus canonical index | no inhabitant |
| `...canonical` | SourceCore:6512 | `[BUILT]` one-point family | approximant |
| `...familyUnion` / `...familyUnion_eq_hull` | SourceCore:6523 / 6555 | `[BUILT]` union and proof it equals the hull | family + hull laws |
| `IUTStage1ExactHullLogVolumeApproximantFamily` | SourceCore:6605 | **structure**; exact family | no inhabitant |
| `...canonicalOfClosed` | SourceCore:6623 | `[BUILT]` one-point exact family for a closed region | exact approximant |

Key limit: none of these constructs the complex-analytic `phi` of IUT III Remark 3.9.5.  The hull is either an intersection over a supplied `isHull` predicate or a product of supplied coordinate sets.

### 1.2 Xi and Phi

| declaration | file:line | body / content | status |
|---|---|---|---|
| `IUTStage1Remark395PossibleImageFamilySource` | SourceCore:7116 | structure: hull operator + possible regions | `[MISSING]` inhabitant |
| `...hullData` | SourceCore:7134 | `[BUILT]` shadow from the operator | — |
| `...familyUnion` | SourceCore:7140 | `[BUILT]` `⋃ i, possibleRegion i` | — |
| `...canonicalHull` | SourceCore:7145 | `[BUILT]` `hullOperator.phi familyUnion` | — |
| `...Phi` | SourceCore:7155 | `[BUILT]` type synonym `IUTStage1HullLogVolumeApproximant hullData familyUnion` | — |
| `...Xi` | SourceCore:7160 | `[BUILT]` type synonym `IUTStage1ExactHullLogVolumeApproximant hullData familyUnion` | — |
| `...canonicalPhi` | SourceCore:7165 | `[BUILT]` canonical approximant | — |
| `...canonicalPhi_approximant_eq_phi` | SourceCore:7171 | `[BUILT]` `rfl` | — |
| `...PhiFamily` / `...XiFamily` | SourceCore:7176 / 7183 | `[BUILT]` type synonyms | — |
| `...HPhi` / `...HXi` | SourceCore:7190 / 7196 | `[BUILT]` family union | — |
| `...HPhi_eq_phi` / `...HXi_eq_phi` | SourceCore:7236 / 7255 | `[BUILT]` both equal the canonical hull, using `familyUnion_eq_hull` | — |
| `IUTStage1Remark395PossibleImageExactXiFamilySource` | SourceCore:7650 | **structure/Prop-like condition**: `logVolume canonicalHull = logVolume familyUnion` | `[MISSING]` inhabitant |
| `...exactApproximant` | SourceCore:7699 | `[BUILT]` from the exact calibration | `[CONDITIONAL]` |
| `...toXiFamily` | SourceCore:7710 | `[BUILT]` one-point `XiFamily PUnit` | `[CONDITIONAL]` |

Thus:

- `Phi` is `[BUILT]` for any supplied `PossibleImageFamilySource`: `canonicalPhi` is a term.
- `Xi` is a type; a term exists only under `IUTStage1Remark395PossibleImageExactXiFamilySource` (or `canonicalOfClosed` when the region is already closed).  The file itself says the general family "cannot manufacture an exact `Xi(P_B)` member from hull monotonicity alone" (SourceCore:7644-7647).
- This is not the paper's `Φ(P)` / `Ξ(P)` of actual holomorphic hulls; it is a finite order/log-volume skeleton.

### 1.3 log-volume

| declaration | file:line | body | dependencies |
|---|---|---|---|
| `IUTStage1RealifiedFrobenioidDegreeObject` | SourceCore:2181 | structure; field `realified_logVolume_eq : realifiedLogVolume = divisorDegree + unitLogVolume` | no inhabitant |
| `...tensorProduct` | SourceCore:2368 | `[BUILT]` adds divisor degrees and unit log-volumes, proves the realified identity | structure |
| `...naiveFrobeniusTensorPower` | SourceCore:2431 | `[BUILT]` multiplies degree and log-volume by `n` | structure |
| `IUTStage1LocalCompactOpenTensorFactorSource` | SourceCore:13713 | structure; `normalizedLogVolume` field, equality to hull log-volume | no inhabitant |
| `IUTStage1CompactOpenNormSquareLocalizedVectorBundleSource` | SourceCore:13755 | structure; factors + nonneg normalized log-volumes + rank > 1 | no inhabitant |
| `...directSummandNorm` | SourceCore:13773 | `[BUILT]` `Real.sqrt normalizedLogVolume` | factor fields |
| `...toNormSquareLocalizedArithmeticVectorBundle` | SourceCore:13781 | `[BUILT]` actual projection | above |
| `...projected_bundleLogVolume_eq_normalizedSum` | SourceCore:13821 | `[BUILT]` bundle log-volume equals finite sum | above |
| `IUTStage1NonarchimedeanLocalCompactOpenLogVolumeSource` | SourceCore:14108 | structure; raw/normalized log-volume fields, integral zero, uniformizer shift | no inhabitant |
| `IUTStage1FiniteExtensionHaarCompactOpenLogVolumeSource` | SourceCore:14212 | structure; Haar log-volume functions are fields, normalization laws are fields | no inhabitant |
| `IUTStage1ArithmeticVectorBundleDeterminantLogVolume` | SourceCore:7792 | structure; rank, tensor power, numeric log-volumes | no inhabitant |
| `...normalizedLogVolume_eq_determinant` | SourceCore:7814 | `[BUILT]` algebraic proof | structure |
| `IUTStage1ArithmeticVectorBundleLocalizationSource` | SourceCore:7899 | structure; `directSummandLogVolume : γ → Real` | no inhabitant |
| `...bundleLogVolume` | SourceCore:7916 | `[BUILT]` `Finset.univ.sum` | field |
| `...toLocalizationLogVolume` | SourceCore:7921 | `[BUILT]` projection | field |
| `...adjustedLogVolume` | SourceCore:7931 | `[BUILT]` `weight * (bundle - structureSheaf)` | field |
| `IUTStage1ArithmeticVectorBundleWeightedDeterminantSource` | SourceCore:8604 | structure; summands, anchor, tensor power | no inhabitant |
| `...ofLocalizationSources` | SourceCore:8615 | `[BUILT]` constructor | localization sources |
| `...determinantLogVolume` | SourceCore:8639 | `[BUILT]` finite sum of adjusted log-volumes | summands |
| `...normalizedLogVolume` | SourceCore:8651 | `[BUILT]` divide by positive tensor power | above |
| `...toDeterminantLogVolume` | SourceCore:8657 | `[BUILT]` projection | above |
| `IUTStage1Remark395HullDeterminantBridgeSource` | SourceCore:33562 | structure; hull operator, qRegion, determinant source, `thetaSigned`, tensor-power bound | no inhabitant |
| `...qRegionLogVolume` | SourceCore:33637 | `[BUILT]` `hullOperator.logVolume qRegion` | field |
| `...familyHullLogVolume` | SourceCore:33642 | `[BUILT]` `hullOperator.logVolume familyHull` | field |
| `...qRegionLogVolume_le_thetaSigned` | SourceCore:33729 | `[BUILT]` one-sided comparison through determinant and tensor bound | fields |
| `IUTStage1ConstructedTheorem311.logVolume` | ConstructedTheorem311:165 | `[BUILT]` `processionAverage + upperSemiLevel` | `ToyIUTIIHodgeArakelovEvaluationData` |
| `IUTStage1FrobenioidShift.LogVolumeChartAudit` | FrobenioidShift:265 | structure/Prop; chart equalities and final inequality | no inhabitant |
| `...logVolumeChartAudit` | FrobenioidShift:298 | `[BUILT]` from an endpoint | endpoint |
| `IUTStage1RecordBoundedFamilyHullDetLogVolumeSource.familyHullLogVolume` | StepXI:74507 | `[BUILT]` `hullData.logVolume familyHull` | record + hull shadow |

The actual *arithmetic formulas* are real; the analytic `logVolume` is always a supplied field, except for the arithmetic definitions above.  There is no construction of a Haar measure on the dependent product in these four files.

### 1.4 ThetaLink

| declaration | file:line | body / content | status |
|---|---|---|---|
| `IUTIIIProcessionChoice` | ConstructedTheorem311:33 | structure: bad place, two `ZMod l` labels, Nat level | `[MISSING]` inhabitant |
| `...ind1Act` | ConstructedTheorem311:71 | `[BUILT]` `zmodLabelTranslate` on `processionLabel` | `ZMod`, choice |
| `...ind2Act` | ConstructedTheorem311:79 | `[BUILT]` translation on `tensorLabel` | above |
| `...ind3Lift` | ConstructedTheorem311:87 | `[BUILT]` adds `n` to `upperSemiLevel` | above |
| `...Ind1Step` / `Ind2Step` / `Ind3Step` | ConstructedTheorem311:132 / 137 / 142 | `[BUILT]` orbit/reachability relations | actions |
| `...processionAverage` | ConstructedTheorem311:147 | `[BUILT]` finite average of Gaussian degrees | `ToyIUTII...` |
| `...logVolume` | ConstructedTheorem311:165 | `[BUILT]` average + upper-semi level | above |
| `...typedCore` | ConstructedTheorem311:201 | `[BUILT]` fills the typed Ind1/Ind2/Ind3 core | above |
| `...pilotValue` / `...possibleImage` | ConstructedTheorem311:225 / 235 | `[BUILT]` value family and its range | above |
| `IUTIIIHorizontalCompatibility` | ConstructedTheorem311:679 | structure with `thetaLink` field at 692 | `[MISSING]` inhabitant |
| `...ofM2` | ConstructedTheorem311:744 | `[BUILT]` constructor | `ToyIUTIIHodgeArakelovEvaluationData` |
| `thetaLink := data.realization.zeroToOneThetaLink` | ConstructedTheorem311:749 | `[BUILT]` term assignment | field of the toy realization |
| `ToyThetaFrobenioidObject` | ThetaHodgeTheater:404 | structure: one `ULift Nat` degree | no inhabitant |
| `...reindexOrderIso` | ThetaHodgeTheater:433 | `[BUILT]` identity-on-degree order isomorphism | above |
| `ToyIUTIHodgeTheaterRealization.zeroToOneThetaLink` | ThetaHodgeTheater:529 | **field**: equivalence between toy degree categories | no inhabitant |
| `...ofStage1HodgeTheaterSource` | ThetaHodgeTheater:548 | `[BUILT]` sets the field to the equivalence of `reindexOrderIso` (563-567) | source + toy categories |
| `SourceThetaLinkCore` (outside the four) | SourceThetaHodgeTheater:5185 | structure: global/local equivalences | no inhabitant |
| `SourceThetaLinkCore.ofTheaters` (outside the four) | SourceThetaHodgeTheater:5234 | `[BUILT]` composes supplied equivalences | source/target theaters |

So the ThetaLink term in the four files is real *as a term*, but its mathematical content is a toy equivalence of `Nat`-degree preorder categories.  It is not a theta-link between Frobenioid categories with actual arithmetic data, and it carries no theta line bundle.

### 1.5 ArithmeticVectorBundle and HDD

| declaration | file:line | body / content | status |
|---|---|---|---|
| `IUTStage1ArithmeticVectorBundleLocalizationLogVolume` | SourceCore:7855 | structure: rank, bundle/structure-sheaf log-volumes, weight | no inhabitant |
| `...adjustedLogVolume` | SourceCore:7865 | `[BUILT]` weighted difference | fields |
| `IUTStage1StructureSheafAdjustedLocalizationSource` | SourceCore:7977 | structure; direct summands, adjustment, weight, rank > 1 | no inhabitant |
| `...toLocalizationSource` | SourceCore:7994 | `[BUILT]` projection | fields |
| `IUTStage1LocalizedArithmeticVectorBundle` | SourceCore:8088 | structure: local ring, summand log-volume, rank > 1 | no inhabitant |
| `...rank` | SourceCore:8098 | `[BUILT]` `Fintype.card γ` | labels |
| `...bundleLogVolume` | SourceCore:8103 | `[BUILT]` finite sum | fields |
| `...toLocalizationSource` | SourceCore:8108 | `[BUILT]` projection | fields |
| `IUTStage1NormSquareLocalizedArithmeticVectorBundle` | SourceCore:8171 | structure: local ring, norm per summand | no inhabitant |
| `...directSummandLogVolume` | SourceCore:8181 | `[BUILT]` `norm ^ 2` | fields |
| `...toLocalizedArithmeticVectorBundle` | SourceCore:8187 | `[BUILT]` projection | fields |
| `IUTStage1ArithmeticVectorBundleWeightedDeterminantSource` | SourceCore:8604 | structure; finite weighted determinant source | no inhabitant |
| `HDDCompositeData` (dependency) | AlgorithmicBridge:824 | structure: `descent : DescentOperationId`, `hullDetBridge : HullDetBridgeData` | no inhabitant |
| `...decompositionAudit` | AlgorithmicBridge:872 | `[BUILT]` records `apply = hullDetBridge.apply`, bound audit | fields |
| `HDDSHECompositeData` (dependency) | AlgorithmicBridge:986 | structure: `sheArrow`, `hdd` | no inhabitant |
| `...ofStructuredSHETransportContext` | AlgorithmicBridge:1006 | `[BUILT]` constructor taking `hdd` | conditional on HDD |
| `IUTStage1SourceHullDetData` | StepXI:36 | structure: `sourceData : HullDetSourceData` | no inhabitant |
| `...ofUnionSubset` | StepXI:46 | `[BUILT]` conditional on a region, subset, volume bound, bridge equality | `[CONDITIONAL]` |
| `...ofUnionHull` | StepXI:71 | `[BUILT]` conditional on a hull operator and volume bound | `[CONDITIONAL]` |
| `...ofHolomorphicHullShadow` | StepXI:156 | `[BUILT]` conditional on a hull shadow, measure equality, bound, bridge equality | `[CONDITIONAL]` |
| `withHDDHullDetBridge` | StepXI:71086 | `[BUILT]` replaces only `hdd.hullDetBridge`; inherits `descent` and all package fields | package-specific |
| `IUTStage1RecordBoundedFamilyHullDetLogVolumeSource` | StepXI:74461 | structure: hull shadow + determinant source + compatibility | no inhabitant |
| `...familyHull` / `...familyHullLogVolume` | StepXI:74500 / 74507 | `[BUILT]` hull and its log-volume | fields |

In the AVB/HDD sections there is **no** `Module`, `Submodule`, `rank`-as-`finrank`, integral lattice, or localization of a vector bundle.  (`SourceCore` does contain unrelated p-adic residue/Haar `Submodule` material around line 20527, not an AVB lattice.)  `rank` is the cardinality of a finite label type.  The explicit comment at SourceCore:7852-7853 says the record does not construct the underlying arithmetic vector bundle; `HDDCompositeData` still stores the bridge as data (AlgorithmicBridge:287-292).

## 2. Correspondence with current S1422 / S1424 / S1479 / S1487

| current node | exact residual | closest promachina declaration | relation | fill? |
|---|---|---|---|---|
| S1422 | `DependentProductScalingChar` (S1422:367) plus rank-`>1` HDD detData | `ArithmeticVectorBundleWeightedDeterminantSource` (SourceCore:8604); `HolomorphicHullLogVolumeShadow` (5988) | finite numeric normalized log-volume only; no Haar product character | no |
| S1424 | geometric source-curve theta line bundle/section (S1424:36-41) | `thetaLink` toy equivalence (ConstructedTheorem311:749; ThetaHodgeTheater:529) | category equivalence, not a line bundle | no |
| S1479 | `O(-D)` line bundle over the q-pilot base (S1479:49-53) | `IUTIIIProcessionChoice.Ind3Step` (142); no line bundle | same directed-reachability shape, different type | no |
| S1487 | scalar equality `O.qPilotLogVolume = OrigXiFPaperQPilotLogVolume C3` (S1487:21-38) | `qRegionLogVolume <= thetaSigned` (SourceCore:33729); `qPilotLogVolume` label (95) | one-sided inequality with free `Real` parameters; no C3 | no |
| S1463 | `scalar_eq` + `signedHull_le` fields | same as S1487 | no scalar equality; no C3 | no |
| S1418/S1215 | rank-`>1` HDD local lattice | `HDDCompositeData` (AlgorithmicBridge:824); AVB `rank := Fintype.card γ` (SourceCore:8098) | bridge card + label cardinality, no module/lattice | no |
| S1476 | already-built rank-2 free AVB localization (see `coord/XI_F_ORIGINAL_ROUTE.md:165`) | promachina AVB records | promachina is weaker; no reason to port | no |

### S1422 (`tmp/sheaf/xif/paper/S1422HDDDetActual.lean`)

Current content:

- `hullLogVolume μ S := μ (hull S)` (S1422:250-252): actual Haar mass of the actual `LocalFieldProductHull.hull`.
- `detDataOfHull` (S1422:262) builds `DetTensorPowerLogVolumeBookkeeping` from an actual additive Haar measure, an actual product-field unit, and a character hypothesis.
- `DependentProductScalingChar s` (S1422:367) is the remaining exact field; `dependentDetDataOfChar` (S1422:374) is conditional on it.

promachina counterpart:

- `IUTStage1ArithmeticVectorBundleDeterminantLogVolume` (SourceCore:7792) is numeric bookkeeping only; its `rank`, `determinantLogVolume`, `positiveTensorPower`, `tensorPowerLogVolume`, `normalizedLogVolume` are fields.
- `IUTStage1ArithmeticVectorBundleWeightedDeterminantSource` (SourceCore:8604) computes a finite sum and normalized quotient, but no measure, no character, no hull.
- `IUTStage1HolomorphicHullLogVolumeShadow.logVolume` (SourceCore:5988-5993) is an abstract `Set α → Real` with monotonicity, not a Haar mass.

**Correspondence**: only the normalized-log-volume identity (`normalized = determinant`, SourceCore:7814) and the finite tensor-power bookkeeping are analogous.  S1422 is strictly stronger on the analytic side.  promachina does not contain `DependentProductScalingChar`, a dependent product Haar measure, or any `distribHaarChar` statement in the four files.

**Verdict**: `[MISSING]` remains.  The four files cannot fill the character or the HDD detData.  A separate, out-of-scope lead is `Foundations/SourceTheorem311.lean:6999-7275` (local Haar character from residue quotient); it is not a dependent-product theorem and was not compiled here.

### S1424 (`tmp/sheaf/xif/paper/S1424ThetaSectionActual.lean`)

Current content:

- `S1424AnalyticThetaLineBundle` (S1424:283) and `s1424AnalyticThetaLineBundle` (S1424:295): actual analytic theta line bundle as a product graph, with `thetaSection t = (t, analyticThetaValue t)` and zero section `(t, 0)`.
- `s1424AnalyticThetaSection` (S1424:315), nonvanishing (329), zero-locus empty (338), and identification with the q_v^(j^2) divisor (346).
- Missing: the source-curve **geometric** theta line bundle/global section, as the header states (S1424:36-41).

promachina counterpart:

- `thetaLink` assignment in ConstructedTheorem311:749.
- `ToyIUTIHodgeTheaterRealization.zeroToOneThetaLink` (ThetaHodgeTheater:529) is an equivalence between toy `Nat`-degree categories (`ToyThetaFrobenioidObject`, 404; `reindexOrderIso`, 433).
- `SourceThetaLinkCore` (SourceThetaHodgeTheater:5185) is a categorical equivalence structure, still not a line bundle.
- No declaration named `LineBundle`, `ThetaLineBundle`, or `ThetaDivisor` exists in `Iut`; `Scheme`, `Picard`, and `Cohomology` are absent from the four files (unrelated `Scheme` names exist in `SourceTrace` and elliptic-curve files).  Case-insensitive `line.?bundle` finds only prose at SourceCore:2364, StepXI:69828, and IUTStage1IUTIVAlgebra:150, plus a false positive in StepXI:13313.

**Correspondence**: none at the object level.  A category equivalence is not a theta line bundle or section.  promachina has no `analyticThetaValue`, no q-disc, no theta divisor.

**Verdict**: `[MISSING]` geometric theta line bundle/section remains.  promachina cannot fill it.

### S1479 (`tmp/sheaf/xif/paper/OrigXiFPaperQPilotObjectPreorderActual.lean`)

Current content:

- `OrigXiFPaperQPilotObject` (S1479:202) with actual boundary, strip, one-column structure, `PaperLineBundleCarrier`, Kummer arrow, q-pilot scalar.
- `OrigXiFPaperCompletionLineBundleCarrier` (S1479:143) is the completion-localized trivial carrier; it is explicitly **not** the paper's `O(-D)` fractional-ideal bundle (S1479:49-53).
- `origXiFPaperQPilotObjectActual` (S1479:367) is an actual inhabitant.
- `origXiFPaperProcessionPreorder` (S1479:329) is an actual `Ind3Step`-based preorder.

promachina counterpart:

- `IUTIIIProcessionChoice` and `ind1Act` / `ind2Act` / `ind3Lift` (ConstructedTheorem311:33,71,79,87), `Ind3Step` (142), `logVolume` (165).  These are actual finite relations/formulas, but on `InitialThetaData`, not on `ConcreteFiniteTheorem311.ProcessionChoice`.
- No `PaperLineBundleCarrier`, no `lineBundle` field, no `O(-D)`, no q-pilot strip in the four files.

**Correspondence**: only the directed-reachability shape (`Ind3Step` as `∃ n, lift n x = y`).  The types and the mathematical data are different.  promachina does not construct a line bundle.

**Verdict**: `[MISSING]` line bundle remains.  promachina cannot fill it; at most it offers a finite `Ind3` template.

### S1487 (`tmp/sheaf/xif/paper/S1487OQPilotScalarEqualityActual.lean`)

Current content:

- `S1487FaithfulScalarEq` (S1487:618): the O-layer `scalar_eq` holds for the faithful one-place bad family.
- `S1487TwoPlaceScalarNe` (S1487:630): two-place counterexample; the scalar equality fails.
- `S1487_no_origXiFScalarExactField` (S1487:733): no `OrigXiFThetaLinkActual` inhabitant over the two-place data.
- The target is the scalar equality between `O.qPilotLogVolume` and `OrigXiFPaperQPilotLogVolume C3` (S1487:21-38).

promachina counterpart:

- `IUTStage1SourceLabels.qPilotLogVolume : QPilotLogVolumeId` (SourceCore:95) is a `String`-backed label.
- `IUTStage1PreLedgerData.qSigned` and `.thetaSigned` are free `Real` fields (`IUTStage1Data.lean:47-48`).
- `IUTStage1Remark395HullDeterminantBridgeSource.qRegionLogVolume_le_thetaSigned` (SourceCore:33729) proves only `qRegionLogVolume <= thetaSigned` with `thetaSigned` a parameter; it is one-sided and has no C3, no completion norm, and no equality.
- `IUTStage1ConstructedTheorem311.logVolume` (165) is a procession average, not the q-pilot scalar.

**Correspondence**: none for the scalar equality.  promachina has no `C3.q`, no completion norm `‖C3.q.q‖`, no bad-place family `∑ |log q_b|`, and no `OrigXiFThetaLinkActual`.

**Verdict**: `[MISSING]` scalar equality remains.  promachina cannot fill it.  The one-sided `qRegionLogVolume <= thetaSigned` could at most be a template for `signedHull_le`, but it does not supply the inputs.

### Adjacent nodes

- **S1463** (`OrigXiFThetaLinkActual`, scalar fields `scalar_eq` + `signedHull_le`): same as S1487; promachina has no scalar equality and no concrete C3.  `[MISSING]`.
- **S1418/S1215** (`HDDLocalLattice`, rank-`>1` localization): promachina has no `HDDLocalLattice`, no module, no lattice; `[MISSING]`.
- **S1476** (actual rank-2 free AVB localization): current project already has an actual rank-2 free arithmetic vector-bundle localization; promachina's AVB is weaker (log-volume labels only), so there is no reason to port it.
- **S1500** (output-dependent HDD lattice): promachina HDD is not output-dependent; `withHDDHullDetBridge` just rewrites a bridge inside a fixed package; `[MISSING]`.

## 3. Can promachina fill HDD / theta?

### HDD: no

Three independent blockers:

1. **HDD is still a bridge card.**  `HDDCompositeData` = `descent` + `hullDetBridge` (`AlgorithmicBridge:824-828`); `HullDetBridgeData` stores `bridge : StructuredCommonTargetBoundBridge` (`AlgorithmicBridge:294-298`).  `withHDDHullDetBridge` only replaces the bridge (`StepXI:71086-71104`).  There is no unconditional `HDDCompositeData` inhabitant in the four files.
2. **No rank-`>1` lattice.**  The AVB records use `directSummandLogVolume : γ → Real` and `rank := Fintype.card γ`; SourceCore:7852-7853 explicitly says the bundle itself is not constructed.  `StepXI` has `LocalCompactOpenTensorFactorSource` and `FiniteExtensionHaarCompactOpenLogVolumeSource`, but their `normalizedLogVolume` / `rawHaarLogVolume` are fields, not a module or lattice construction.
3. **No dependent-product character.**  S1422's exact residual is `DependentProductScalingChar` (S1422:367), not present in the four files.  The local Haar-character theorem in `Foundations/SourceTheorem311.lean:6999-7275` is a possible donor, but it is local, outside the four, and has no dependent-product version.

Therefore, even if one ports every hull/log-volume declaration in the four files, the HDD first field (rank-`>1` lattice) and S1422's character remain missing.

### Theta: no

1. No theta line bundle, theta section, or theta divisor is declared anywhere in the snapshot (`LineBundle` declaration grep = 0).  `Scheme` names exist only in unrelated elliptic/SourceTrace files; `Scheme`, `Picard`, `Cohomology` are 0 in the four files.
2. `thetaLink` in the four files is a toy equivalence between `Nat`-degree preorder categories (`ThetaHodgeTheater:404,433,529,563`), not a theta-link between Frobenioid categories with arithmetic data.
3. S1487's target is a scalar equality against a concrete completion q; promachina has only labels and free `Real` fields.
4. S1424's geometric source-curve theta line bundle/section is absent; the current S1424 analytic graph model is already stronger than anything in promachina.

## 4. What is portable, and at what cost

### Grade A: pure Mathlib/Set/Real finite bookkeeping (low risk, but not paper-level)

These declarations depend only on Mathlib (`Set`, `ClosureOperator`, `Real`, `Finset`, `Equiv`) and on each other:

- `Iut.Stage1.IUTStage1Remark395HolomorphicHullOperator.toClosureOperator` (SourceCore:3026), `...transport` (3125).
- `Iut.Stage1.IUTStage1Remark395HolomorphicHullSystem.phi` (3196) and its laws (3202-3299).
- `Iut.Stage1.IUTStage1Remark395DirectProductHullSystemSource` (3470) with `productHull` (3487), `coordinateProjection` (3493), `intersectionParameter` (3500), `toProductHullSystemSource` (3558), `toHolomorphicHullSystem` (3570), and the endpoint theorem (3584).
- `Iut.Stage1.IUTStage1HolomorphicHullLogVolumeShadow` (5988) with `ofRemark395Operator` (6000), `hullRegion` (6027), `toRegionHullOperator` (6134), `toRegionMeasure` (6145).
- `Iut.Stage1.IUTStage1HullLogVolumeApproximant` (6311), `canonical` (6329), `IUTStage1ExactHullLogVolumeApproximant` (6405), `canonicalOfClosed` (6419), `IUTStage1HullLogVolumeApproximantFamily` (6496), `canonical` (6512), `familyUnion_eq_hull` (6555), `IUTStage1ExactHullLogVolumeApproximantFamily` (6605).
- `Iut.Stage1.IUTStage1Remark395PossibleImageFamilySource` (7116) with `Phi` (7155), `Xi` (7160), `canonicalPhi` (7165), `PhiFamily` (7176), `XiFamily` (7183), `HPhi` (7190), `HXi` (7196).
- `Iut.Stage1.IUTStage1Remark395PossibleImageExactXiFamilySource` (7650), `exactApproximant` (7699), `toXiFamily` (7710).
- `Iut.Stage1.IUTStage1ArithmeticVectorBundleDeterminantLogVolume` (7792) and its normalized theorem (7814).
- `Iut.Stage1.IUTStage1ArithmeticVectorBundleLocalizationLogVolume` (7855), `...LocalizationSource` (7899), `...StructureSheafAdjustedLocalizationSource` (7977), `...LocalizedArithmeticVectorBundle` (8088), `...NormSquareLocalizedArithmeticVectorBundle` (8171).
- `Iut.Stage1.IUTStage1ArithmeticVectorBundleWeightedDeterminantSource` (8604), `ofLocalizationSources` (8615), `determinantLogVolume` (8639), `normalizedLogVolume` (8651), `toDeterminantLogVolume` (8657).
- `Iut.Stage1.IUTStage1Remark395HullDeterminantBridgeSource` (33562) and its one-sided comparison (33729), after porting the above.

Caveats: namespace `Iut.Stage1` vs current `LeanFormal.IUT`; Lean 4.30 vs 4.32.2; no compilation was run.  The declarations are finite bookkeeping and must not be described as the paper's Xi/Phi/hull/log-volume.

### Grade B: requires promachina `RealLineCopy` / package layer (high cost)

These depend on `Copy`, `Region`, `RegionMeasure`, `HullOperator`, `AlgorithmicOutput`, `HullDetBridgeData`, `HDDCompositeData`, `QualitativeData`, etc.  Current project has **no** `RealLineCopy`, `RegionMeasure`, `HullOperator`, `HullDetBridgeData`, or `AlgorithmicOutput` (grep in `LeanFormal` = 0).  Porting would require a substantial foundation layer:

- `Iut.Stage1.IUTStage1SourceHullDetData` (StepXI:36), `ofUnionSubset` (46), `ofUnionHull` (71), `ofHolomorphicHullShadow` (156).
- `Iut.Stage1.IUTStage1SourceHullDetObligations` (StepXI:1658).
- `Iut.Stage1.IUTStage1RecordBoundedFamilyHullDetLogVolumeSource` (StepXI:74461), `familyHull` (74500), `familyHullLogVolume` (74507).
- `Iut.Stage1.IUTStage1SourcePackage.withHDDHullDetBridge` (StepXI:71086).
- `Iut.Stage1.IUTStage1FrobenioidShift.MultiradialThetaHullEndpoint` (36) and `LogVolumeChartAudit` (265).
- `Iut.Stage1.IUTStage1ConstructedTheorem311` `thetaLink` (749), because it depends on `ToyIUTIHodgeTheaterRealization` and `InitialThetaData`; the toy layer itself is in `Foundations/ThetaHodgeTheater.lean`.

### Grade C: do not port as a construction

- `Iut.Stage1.IUTStage1SourceLabels.qPilotLogVolume` (SourceCore:95): a label.
- `HDDCompositeData` (AlgorithmicBridge:824): a bridge card.
- `withHDDHullDetBridge` (StepXI:71086): a bridge rewrite, not an HDD construction.
- `ToyIUTIHodgeTheaterRealization.zeroToOneThetaLink` (ThetaHodgeTheater:529): toy degree equivalence, not the paper's theta-link.
- The AVB structures (SourceCore:7792, 7855, 7899, 7977, 8088, 8171, 8604): log-volume bookkeeping, not vector bundles.

## 5. Out-of-scope sibling modules worth a separate audit

The snapshot's metadata (`review-1fa6387f.json:31-39`) lists direct reuse candidates that are *not* among the four files.  Two are directly relevant to this audit:

1. `Iut/Foundations/SourceIUTIIIRemark395HolomorphicHull.lean`
   - `SourceIUTIIIRemark395PrincipalRadiusGeometry` (45), `radiusRegion` (81), `hullRadius` (87), `phi` (96): an actual hull from a scalar-radius geometry; finite radius becomes `lambda * O` (227); `toHolomorphicHullSystem` (310).
   - `SourceIUTIIITheorem311Remark395Construction` (397): actual quotient-indexed possible-image family (456), family union (471), canonical hull (483), `canonicalPhi` (487), `Phi` (495), `Xi` (500); `Xi` nonempty only under `ExactXiCriterion` (656) or `familyUnion_isHull` (627).
   - This is a more substantive hull kernel, but still parameterized by `SourceIUTIIITheorem311iEvaluation`; no inhabitant of that evaluation is provided in the file.
2. `Iut/Foundations/SourceIUTIIIRemark395WeightedDeterminant.lean`
   - `SourceIUTIIIRealifiedArithmeticLine` (59), `arithmeticDegree` (81), `SourceIUTIIIRemark395WeightedDeterminantData` (188), `summandRegion` (217), `hullDeterminantLine` (250), `adjustedDeterminantLine` (264), `commonTensorDegree` (284), `weightedDeterminantLine` (341), `normalizedDeterminantLine_arithmeticDegree` (402), `weightedDeterminantLine_arithmeticDegree` (410).
   - This is a concrete `Finsupp`-level determinant/log-volume construction, still not a scheme-level arithmetic vector bundle and not an HDD lattice.
3. `Iut/Foundations/AlgorithmicBridge.lean` HDD definitions (294, 450, 824, 986) are the dependency layer, not a construction of the paper's HDD.
4. `Iut/Foundations/SourceTheorem311.lean:6999-7275` local Haar character, as noted above.

A follow-up audit of these sibling modules is required before claiming any port.  They are outside the four-file scope and were only read for dependency/possibility assessment.

## 6. Verification status

| item | status |
|---|---|
| `statement_compiles` | **not run** (read-only audit; no Lean invocation) |
| `proof_body_checked` | **not run** |
| `kernel_closed` | **not run** |
| comparator / target lock | **not run** |
| `target_accepted` | **false** |

This report makes no compile or axiom claim.  All line numbers come from the snapshot files as read on 2026-10-31.  The snapshot's own full build is recorded as passed with Lean 4.30.0 in `review-1fa6387f.json:14-24`; that is an upstream build, not a build in this workspace.

## 7. One executable next step

If the finite hull/Phi bookkeeping is useful as scaffolding, the lowest-risk port is:

1. Copy `IUTStage1Remark395HolomorphicHullSystem` + `IUTStage1Remark395DirectProductHullSystemSource` + `IUTStage1HolomorphicHullLogVolumeShadow` + `IUTStage1HullLogVolumeApproximant` (SourceCore:3182-6700) into a standalone module under `tmp/sheaf/...`;
2. compile it alone and run `#print axioms` on the endpoint theorems;
3. do **not** port `HDDCompositeData`, `withHDDHullDetBridge`, or the toy `thetaLink` as a fix for S1422/S1424/S1479/S1487.

For the real gaps, the next executable steps remain in the current project: a rank-`>1` HDD localization for S1422/S1215, a geometric theta line bundle/section for S1424/S1479, and a concrete q-pilot scalar equality for S1487.  promachina 1fa does not supply them.
