import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ComparisonGapReduction
import LeanFormal.IUT.ABCBridge.Bridge.Cor312GapDictionaryLayer
import LeanFormal.IUT.Audit.Status

/-!
# S3137: paper-faithful route dependency map (task-73)

DEPENDENCY MAP for the paper route
  R1 -> Cor312ToABCBridgeInterfaceV2 -> cardP/ABC
with INDEX ids for every route field, mapping to existing tree objects and
marking constructed vs missing.  NOTE: the names `Cor312EpsilonArithmeticComparisonV2`
and `Cor312ToABCBridgeInterfaceV2` are NOT yet in the tree; the current V2 =
`Cor312EpsilonArithmeticComparisonAdditive` (contract v2, additive height form)
and `Cor312ToABCBridgeInterface` (production, EXIT0).  Mapping is against those;
if mainline renames to V2 the ids below stay valid (field names unchanged).

## Route fields
1. `comparisonRegion`: CONSTRUCTED — `normalizedComparisonRegion W scaleShift
   unitRegion ∪ {logShellPoint}` (W : IQHullLogVolumeInterface).  Tree hull
   interface realized on the actual finite-place tensor carrier
   (FinitePlaceIQHullInterface); θ-side readouts: S3137 qTheta bridge
   (`qThetaPilotLogVolumeComparison_of_modelMap`, `thetaPilotHullLogVolumeReal`),
   S3132 hull log-volume (`sourceHullRealLogVolume`, `paperHullRealLogVolume`).
2. `logShellPoint` (named paper datum): MISSING as an actual θ-pilot point of
   x=a/c.  Candidates: S3131 QC/HC readouts (`S3131PaperRegionalQ/Hull`),
   S3129 hull log-volume interface point, old S2607/S2721 bridge-data skeletons.
3. `height_le_normalizedRegionVolume` (V1) / additive V2 form
   (`height ≤ (1+ε)·regionVolume + A`): NOT proved.  V1 uniform form is
   REFUTED (production probe + `Cor312ComparisonGapReduction.cor312Gap1_exists_
   carrier_arithmeticWeight_gt_normalizedComparisonRegionVolume`,
   `cor312Gap1_not_forall_arithmeticWeight_le_normalizedComparisonRegionVolume`);
   V2 additive needs an actual dictionary/point bound (see gap survey).
4. `regionVolume_le_normalizedWeight`: NOT proved in full.  Proved reductions in
   production: `cor312Gap2_hull_logVolume_le_normalizedComparisonRegion`,
   `cor312Gap2_scaleShift_unitRegion_logVolume_le_normalizedComparisonRegion`,
   `cor312Gap2_regionVolume_le_add_of_subadditive`,
   `cor312Gap2_regionVolume_le_normalizedWeight_of_split_pointBound_unitRegionBound`
   (conditional on split + point bound + unit-region bound),
   `cor312Gap2_pointBound_of_singletonVolume_le_logHeight`, plus S3137 θ-side
   `thetaPilotHullLogVolumeReal`/`qPilotLogVolumeReading` bridge and S3131 QC/HC.
5. `hullData`: CONSTRUCTED existing tree hull/log-volume interface; θ-bound term
   `(W.logVolume W.hull).toReal` finite (Cor 3.12 finiteness theorem,
   `Cor312EpsilonArithmeticComparison.comparisonRegion_logVolume_lt_top`).
6. bridge package: `Cor312ToABCBridgeInterface` with conditional closures
   `cor312ToABCBridge_heightBound`, `cor312ToABCBridge_abcConjecture`,
   `cor312ToABCBridge_abcLogConjecture`, `cor312ToABCBridge_rpowBound` —
   CONDITIONAL on the two comparison fields; nothing unproved hidden.

## Old frontier/gap survey (statements vs route fields)
* `Cor312ComparisonGapReduction` (production, proofs): gap-2 reductions above are
  PROVED; gap-1 `cor312Gap1_height_le_normalizedRegionVolume_of_weight_bound` is
  PROVED as a conditional reduction from an arithmeticWeight bound;
  `cor312GapAssembly_epsilonComparisonOfReducedInputs` CONSTRUCTS the per-ε
  comparison from reduced inputs.  Gap-1 uniform statements are REFUTED (kept
  negative).
* `Cor312GapDictionaryLayer` (production, proofs): dictionary non-universality
  PROVED (`cor312GapDict_weightDictionary_not_universal`,
  `cor312GapDict_pointHeightDictionary_not_universal`) — the weight/point-height
  dictionary is a genuine hypothesis, not a theorem; positive directions
  `cor312GapDict_weightDictionary_iff_scalingSeparated`,
  `cor312GapDict_sourcePointBound_of_degree_le_height`,
  `cor312GapDict_sourcePointBound_of_additiveBound` are PROVED reductions.
* S2607 (`S2607SignedGapActual`, `S2607HeightUpperTargetActual`, Hmap/M2 files):
  signed gap targets (`SignedGap1_height`, `SignedGap2Target`, `SignedVolume`) map
  to route fields 3/4 on the θ-pilot carrier; old pre-gate skeletons, not gate
  imports — re-usable only as statement templates.
* S2720/S2721/S2722 (`BridgeSkeleton/BridgeHaar/BridgeActualObj/BridgeData/
  Hpoint/HunitD/Gap2Assembly`): bridge skeletons instantiating
  `Cor312ToABCBridgeInterface` from S2586/epsilonComparison and bridge data;
  they map to field 6 (bridge package) and fields 3/4 (Hpoint/HunitD inputs).
  Old frontier files, not gate imports; their remaining inputs are exactly
  fields 2-4 above.

VERDICT: field 1 and hull interface CONSTRUCTED; field 2 (logShellPoint as an
actual θ-pilot point/dictionary instance) is the primary missing object; field 3
(additive V2 height comparison) and field 4's point-bound half are the two named
residuals; all proved reductions are in production files listed above.  No
circularity: the bridge interface is inhabited iff ABC holds
(`cor312ToABCBridgeInterface_nonempty_iff_abcConjecture`), so the route is a
faithful conditional reduction, not a proof.
Data only; no proof content.  WRITE-ONLY.
-/

namespace LeanFormal.IUT.XiFPaper.S3137PaperRouteMapActual

open LeanFormal.IUT.Audit

/-- Route-field -> tree-object/status map (data). -/
def S3137PaperRouteFieldMap : List (String × String) :=
  [ ("comparisonRegion", "CONSTRUCTED: normalizedComparisonRegion (scaleShift '' (unitRegion ∪ {logShellPoint})); hull interface FinitePlaceIQHullInterface; theta readouts S3137 qTheta bridge + S3132 paperHullRealLogVolume/sourceHullRealLogVolume; S3131 QC/HC."),
    ("logShellPoint", "MISSING named paper datum: actual theta-pilot point of x=a/c; candidates S3131PaperRegionalQ/Hull, S3129 hull point, S2607/S2721 skeletons."),
    ("height_le_normalizedRegionVolume (V2 additive)", "NOT PROVED; V1 uniform REFUTED (cor312Gap1_* counterexample theorems); proved conditional reduction cor312Gap1_height_le_normalizedRegionVolume_of_weight_bound; needs actual dictionary/point bound (Cor312GapDictionaryLayer non-universality proved)."),
    ("regionVolume_le_normalizedWeight", "NOT PROVED in full; proved reductions cor312Gap2_hull_logVolume_le_normalizedComparisonRegion / cor312Gap2_scaleShift_unitRegion... / cor312Gap2_regionVolume_le_add_of_subadditive / cor312Gap2_regionVolume_le_normalizedWeight_of_split_pointBound_unitRegionBound / cor312Gap2_pointBound_of_singletonVolume_le_logHeight; theta bound via S3137/S3132/S3131 readouts."),
    ("hullData", "CONSTRUCTED: actual IQHullLogVolumeInterface; hull volume finite (Cor 3.12 finiteness); thetaBound = (W.logVolume W.hull).toReal."),
    ("bridge package", "CONSTRUCTED: Cor312ToABCBridgeInterface + conditional closures cor312ToABCBridge_heightBound / _abcConjecture / _abcLogConjecture / _rpowBound; inhabited iff ABCConjecture.") ]

/-- Old frontier/gap file -> route field + status map (data). -/
def S3137PaperRouteOldFileSurvey : List (String × String) :=
  [ ("Cor312ComparisonGapReduction", "fields 3/4: gap-2 reductions and conditional gap-1 reduction PROVED; uniform gap-1 REFUTED (kept negative); cor312GapAssembly_epsilonComparisonOfReducedInputs constructs per-eps comparison from reduced inputs."),
    ("Cor312GapDictionaryLayer", "fields 2-4: dictionary non-universality PROVED (weightDictionary_not_universal, pointHeightDictionary_not_universal); positive reductions weightDictionary_iff_scalingSeparated, sourcePointBound_of_degree_le_height/_additiveBound PROVED."),
    ("S2607SignedGapActual / S2607HeightUpperTargetActual / S2607HmapActual", "fields 3/4 on the theta-pilot carrier (SignedGap1_height, SignedGap2Target, SignedVolume); old pre-gate skeletons, statement templates only."),
    ("S2720Bridge* / S2721Bridge* / S2722Gap2*", "field 6 bridge skeletons + fields 3/4 inputs (Hpoint/HunitD); old frontier files, not gate imports; remaining inputs = fields 2-4.") ]

end LeanFormal.IUT.XiFPaper.S3137PaperRouteMapActual

namespace LeanFormal.IUT.Audit

/-- INDEX.PAPER-ROUTE: comparisonRegion (constructed). -/
def INDEX_PAPER_ROUTE_comparisonRegion : Obligation :=
  { id := "INDEX.PAPER-ROUTE.comparison-region"
    source := "IUT IV section 2; Cor312ToABCBridgeInterface.lean (normalizedComparisonRegion); FinitePlaceIQHullInterface"
    status := VerificationStatus.interface
    note := "CONSTRUCTED: comparison region = scaleShift '' (unitRegion ∪ {logShellPoint}) on the actual hull interface; theta-side readouts supplied by S3137 qTheta bridge (qThetaPilotLogVolumeComparison_of_modelMap, thetaPilotHullLogVolumeReal), S3132 paperHullRealLogVolume/sourceHullRealLogVolume, S3131PaperRegionalQ/Hull. Owned by mainline+abc+lattice; not a residual."
    dependsOn := ["Cor312ToABCBridgeInterface", "S3137PaperRouteMapActual"] }

/-- INDEX.PAPER-ROUTE: logShellPoint (missing named datum). -/
def INDEX_PAPER_ROUTE_logShellPoint : Obligation :=
  { id := "INDEX.PAPER-ROUTE.log-shell-point"
    source := "Cor312EpsilonArithmeticComparison.logShellPoint field; IUT IV section 2; S2607/S2721 skeletons; S3131 QC/HC"
    status := VerificationStatus.pending
    note := "MISSING named paper datum: the actual θ-pilot point attached to x=a/c whose log-volume/local degree is compared with the height. Candidates: S3131PaperRegionalQ/Hull readouts, S3129 hull point, S2607/S2721 bridge-data skeletons. Primary missing object of the paper route; NOT ABC-strength by itself."
    dependsOn := ["INDEX.PAPER-ROUTE.comparison-region", "S3131PaperNormalizedComparisonActual"] }

/-- INDEX.PAPER-ROUTE: height comparison (V2 additive). -/
def INDEX_PAPER_ROUTE_heightComparison : Obligation :=
  { id := "INDEX.PAPER-ROUTE.height-comparison"
    source := "IUT IV Theorem A (additive bounded-discrepancy); ABCHeightArithmeticWeightComparison.ABCHeightWeightAdditiveBoundV2; Cor312ComparisonGapReduction.cor312Gap1_*"
    status := VerificationStatus.pending
    note := "NOT PROVED. V1 uniform valuation bound REFUTED (cor312Gap1_exists_carrier_arithmeticWeight_gt_normalizedComparisonRegionVolume, cor312Gap1_not_forall_arithmeticWeight_le_normalizedComparisonRegionVolume; probe H1UniformValuationBoundCounterexampleProbe). V2 additive shape height <= (1+eps)*regionVolume + A; proved conditional reduction cor312Gap1_height_le_normalizedRegionVolume_of_weight_bound; needs actual dictionary/point bound (Cor312GapDictionaryLayer non-universality proved). Residual (paper input), not ABC-strength here."
    dependsOn := ["INDEX.PAPER-ROUTE.log-shell-point", "Cor312ComparisonGapReduction"] }

/-- INDEX.PAPER-ROUTE: region-volume / weight comparison. -/
def INDEX_PAPER_ROUTE_regionVolumeWeight : Obligation :=
  { id := "INDEX.PAPER-ROUTE.region-volume-weight"
    source := "IUT IV section 2; Cor312ComparisonGapReduction.cor312Gap2_*; Cor312GapDictionaryLayer"
    status := VerificationStatus.pending
    note := "NOT PROVED in full. Proved reductions: cor312Gap2_hull_logVolume_le_normalizedComparisonRegion, cor312Gap2_scaleShift_unitRegion_logVolume_le_normalizedComparisonRegion, cor312Gap2_regionVolume_le_add_of_subadditive, cor312Gap2_regionVolume_le_normalizedWeight_of_split_pointBound_unitRegionBound (conditional on split + point bound + unit-region bound), cor312Gap2_pointBound_of_singletonVolume_le_logHeight. Theta bound term via S3137 qTheta bridge + S3132 hull volumes + S3131 QC/HC. Missing: point bound/dictionary instance (Cor312GapDictionaryLayer non-universality)."
    dependsOn := ["INDEX.PAPER-ROUTE.log-shell-point", "Cor312ComparisonGapReduction", "Cor312GapDictionaryLayer", "S3137QThetaComparisonBridgeActual"] }

/-- INDEX.PAPER-ROUTE: bridge package (conditional closure). -/
def INDEX_PAPER_ROUTE_bridgePackage : Obligation :=
  { id := "INDEX.PAPER-ROUTE.bridge-package"
    source := "Cor312ToABCBridgeInterface (production); cor312ToABCBridge_abcConjecture / _heightBound / _rpowBound"
    status := VerificationStatus.interface
    note := "CONSTRUCTED conditional package: Cor312ToABCBridgeInterface = carrier + IQHullLogVolumeInterface + per-eps Cor312EpsilonArithmeticComparison; inhabited iff ABCConjecture (cor312ToABCBridgeInterface_nonempty_iff_abcConjecture); closures cor312ToABCBridge_heightBound/_abcConjecture/_abcLogConjecture/_rpowBound. Consumes fields 1-4; nothing unproved hidden. CardP is NOT an input of this route."
    dependsOn := ["INDEX.PAPER-ROUTE.comparison-region", "INDEX.PAPER-ROUTE.height-comparison", "INDEX.PAPER-ROUTE.region-volume-weight"] }

/-- Route dependency map record (task-73). -/
def S3137PaperRouteDependencyMap : Obligation :=
  { id := "INDEX.PAPER-ROUTE.dependency-map"
    source := "Cor312ToABCBridgeInterface.lean; Cor312ComparisonGapReduction.lean; Cor312GapDictionaryLayer.lean; S2607*/S2720*/S2721*/S2722* frontier files; S3137 qTheta bridge; S3131/S3132/S3134 readouts"
    status := VerificationStatus.interface
    note := "DEPENDENCY MAP for R1 -> Cor312ToABCBridgeInterfaceV2 (current names: Cor312EpsilonArithmeticComparisonAdditive / Cor312ToABCBridgeInterface; V2 literals NOT yet in tree) -> cardP/ABC: fields comparison-region (CONSTRUCTED), log-shell-point (MISSING datum), height-comparison (NOT PROVED; V1 refuted, V2 additive conditional), region-volume-weight (NOT PROVED; reductions proved), hullData (CONSTRUCTED), bridge package (CONSTRUCTED conditional). Old frontier files mapped in S3137PaperRouteOldFileSurvey. No circularity; route is a faithful conditional reduction."
    dependsOn := ["INDEX.PAPER-ROUTE.bridge-package", "S3137PaperRouteMapActual"] }

end LeanFormal.IUT.Audit