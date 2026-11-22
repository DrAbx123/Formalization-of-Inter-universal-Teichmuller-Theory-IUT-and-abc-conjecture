/-!
# S3139: route residual list v4 — Option-B COMPLETE (data only; frozen pair 14041)

Per Lead/lattice: Option-B is complete (qpilot concrete donor CITABLE,
abc base-unit fill CITABLE).  Updated residual status after consuming both:

DISCHARGED / AVAILABLE (reuse; no re-proof):
* FT.M1.model (in-model): S3139ModelM1DischargeActual.sourceModelM1Evidence_holds.
* Option-B concrete donor evidence path: S3139OptionBCompleteActual consumes
  S3133M1ConcretePrimeMatchActual (S3131BadTensorPrimeMatch_concrete:68; donor
  record S3133M1ConcreteDonor:79) and S3135TreeModelBaseUnitScalingActual
  (s3135_treeModelBaseUnitScaling:17, baseUnit = -1, unconditional).
* FT.fourth-triangle.hull-side.model: CardHull sourceSignedHullLogVolume_le_sourceSignedImageLogVolume:215
  via S3139HaarModelConsumptionActual.s3139_modelHullVolume_le_imageVolume.
* FT.route.comparison-invariance / measure-invariance: carried explicitly as named
  residuals (mainline S3131RouteComparisonInvarianceHypothesis / abc
  S3135ComparisonMeasureInvariance); no implicit assumption anywhere.
STILL OPEN (exact):
* FT.M1 general (arbitrary frozen input; qpilot S3133M1ContractSeparatedMissing/S3133M1Remaining).
* FT.M1 concrete donor exact fields: index_eq : C3.tensorIndex = Bad (...) and p_eq : C3.p = 5
  (S3133M1ConcreteDonor fields; explicit input, not proved unconditionally).
* FT.M1.capsule-label-link (contract-separated Capsule j.val <-> Bad/V).
* FT.M0.same-C (mainline R1).
* FT.stage4.unit-map (S3136LGPGlobalUnitsToLocalUnitsActual.lgpGlobalUnitsToLocalUnits).
* FT.fourth-triangle arithmetic inputs (hull value + (xi-f) inclusion for the route instance).
* FT.route.comparison/measure-invariance (mainline/abc).

**Component, not paper object.**  Frozen registry pair 14041; no registry edits.
No sorry/axiom/True/PUnit/toy carrier (data file).
-/

namespace LeanFormal.IUT.XiFPaper.S3139RouteResidualUpdateV4Actual

/-- V4 open residual list after Option-B completion. -/
def routeOpenResidualsV4 : List (String × String × String) :=
  [ ("FT.M1.model", "DISCHARGED (Option-B complete)",
      "S3139ModelM1DischargeActual.sourceModelM1Evidence_holds; S3139OptionBCompleteActual.sourceOptionBComplete"),
    ("FT.M1.concrete-donor", "CONDITIONAL (explicit donor input)",
      "S3133M1ConcreteDonor index_eq/p_eq fields; S3131BadTensorPrimeMatch_concrete"),
    ("FT.M1.general", "OPEN", "qpilot S3133M1ContractSeparatedMissing/S3133M1Remaining"),
    ("FT.M1.capsule-label-link", "OPEN (contract-separated)", "Capsule j.val <-> Bad/V link"),
    ("FT.M0.same-C", "OPEN", "mainline R1 same-C identification"),
    ("FT.stage4.unit-map", "OPEN", "S3136LGPGlobalUnitsToLocalUnitsActual.lgpGlobalUnitsToLocalUnits"),
    ("FT.fourth-triangle.hull-side.model", "AVAILABLE (CardHull reuse)", "sourceSignedHullLogVolume_le_sourceSignedImageLogVolume:215"),
    ("FT.fourth-triangle.inputs", "OPEN", "hull value + (xi-f) inclusion for the route instance"),
    ("FT.route.comparison-invariance", "OPEN", "mainline S3131RouteComparisonInvarianceHypothesis"),
    ("FT.route.measure-invariance", "OPEN", "abc S3135ComparisonMeasureInvariance") ]

end LeanFormal.IUT.XiFPaper.S3139RouteResidualUpdateV4Actual
