/-!
# S3139: route residual list v3 — Option-B in-model M1 discharge (data only)

Per Lead directive: update the residual list with the new model-route evidence so
FT.M1/m1 slot is DISCHARGED IN-MODEL (Option-B) and only the genuinely open items
remain.  Evidence (prior-art check §7.9, all existing and green):
* S3133ExistingModelAdaptationActual.lean (results:159686): S3133TreeModelM1Datum:95,
  S3133TreeModelM1_constructible:103 (in-model place-to-moduli datum + injectivity).
* S3133ModelM1PlaceToModActual.lean (results:155535): modelPlaceToModDatum:46,
  modelPlaceToMod_injective:54, S3133ModelM1_constructible:59 (V-basis M1 datum).
* S3135ModelSkeletonInterfaceActual.lean (EXIT=0): model hull/Haar/scaling interface.
* S3133ExistingModelAdaptationActual.lean:57-82: tree-model Haar data, scaling = 1,
  theta q = 1 (reuse of SourceUnitRegionHaarDataActual model).
* CardHullRealSignedLogVolume.lean:215 sourceSignedHullLogVolume_le_sourceSignedImageLogVolume
  + :231 sourceSignedImageComparison_iff_realParts_eq (in-model xi-f direction).
* CardAMPLThetaBoundSupply.lean:193 cor312Conclusion (in-model supply conclusion).

NEW STATUS: FT.M1 (in-model, Option-B) DISCHARGED by
S3139ModelM1DischargeActual.sourceModelM1Evidence_holds; fourth-triangle hull side
(in-model) available via S3139HaarModelConsumptionActual.sourceModelRouteEvidence.
STILL OPEN: FT.M1 general (arbitrary frozen input; not the model), FT.M0.same-C
(mainline R1), FT.M1.capsule-label-link (contract-separated), FT.stage4.unit-map,
FT.fourth-triangle arithmetic inputs (hull value + (xi-f) inclusion for the route
instance; in-model only the hull side direction is supplied).

**Component, not paper object.**  Registry frozen 13129; no registry edits.
No sorry/axiom/True/PUnit/toy carrier (data file).
-/

namespace LeanFormal.IUT.XiFPaper.S3139RouteResidualUpdateV3Actual

/-- V3 open residual list after Option-B in-model M1 discharge. -/
def routeOpenResidualsV3 : List (String × String × String) :=
  [ ("FT.M1.model", "DISCHARGED IN-MODEL (Option-B)",
      "S3139ModelM1DischargeActual.sourceModelM1Evidence_holds; evidence S3133TreeModelM1Datum/S3133ModelM1_constructible"),
    ("FT.M1.general", "OPEN", "arbitrary frozen input; qpilot S3133M1ContractSeparatedMissing/S3133M1Remaining"),
    ("FT.M1.capsule-label-link", "OPEN (contract-separated)", "Capsule j.val <-> Bad/V link"),
    ("FT.M0.same-C", "OPEN", "mainline R1 same-C identification"),
    ("FT.stage4.unit-map", "OPEN", "S3136LGPGlobalUnitsToLocalUnitsActual.lgpGlobalUnitsToLocalUnits"),
    ("FT.fourth-triangle.hull-side.model", "AVAILABLE IN-MODEL", "CardHull sourceSignedHullLogVolume_le_sourceSignedImageLogVolume:215"),
    ("FT.fourth-triangle.inputs", "OPEN", "hull value + (xi-f) inclusion for the route instance"),
    ("FT.route.comparison-invariance", "OPEN", "mainline S3131RouteComparisonInvarianceHypothesis / abc S3135ComparisonMeasureInvariance"),
    ("FT.route.measure-invariance", "OPEN", "abc S3135ComparisonMeasureInvariance") ]

end LeanFormal.IUT.XiFPaper.S3139RouteResidualUpdateV3Actual
