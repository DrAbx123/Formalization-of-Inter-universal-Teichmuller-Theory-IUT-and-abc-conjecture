/-!
# S3139: route ids update 4 — Option-B completion + pin correction (data only; pins 14041)

Ids for lattice's next approved re-pin (lattice already recorded the model-route ids
in S3137ModelRouteIdsNoteActual with the 14041 correction).

* INDEX.FT.OptionB.concrete-donor-consumption -> S3139OptionBCompleteActual:
  s3139_baseUnitScaling_available, s3139_baseUnitScaling_baseUnit,
  s3139_baseUnitScaling_nontrivial, s3139_badTensorPrimeMatch_of_donor,
  SourceOptionBComplete + sourceOptionBComplete + sourceOptionBComplete_modelM1.
  Evidence reuse: S3133M1ConcretePrimeMatchActual (S3131BadTensorPrimeMatch_concrete:68,
  S3133M1ConcreteDonor:79; CITABLE 5 decls) and S3135TreeModelBaseUnitScalingActual
  (s3135_treeModelBaseUnitScaling:17, baseUnit = -1; CITABLE 2 decls).
* INDEX.FT.route.residual-v4 -> S3139RouteResidualUpdateV4Actual.routeOpenResidualsV4
  (Option-B complete; M1.model DISCHARGED; M1 concrete donor conditional on explicit
  index_eq/p_eq fields; remaining: general M1, capsule-label link, M0, stage4 map,
  fourth-triangle arithmetic inputs, comparison/measure invariance).
* INDEX.PIN.correction-14041 -> S3139PinCorrectionActual.currentFrozenPin /
  supersededPinSize / pin_corrected (frozen pair 14041, src 4AF7EC60, olean 5991A075;
  supersedes earlier 13129 references in this stream).
* INDEX.REUSE.OptionB-audit -> S3139PriorArtAudit3Actual.optionBPriorArt.

**Component, not paper object.**  No sorry/axiom/True/PUnit/toy carrier (data file).
-/

namespace LeanFormal.IUT.XiFPaper.S3139RouteIdsUpdate4Actual

/-- Route ids update 4: (index id, declarations, file). -/
def routeIdsUpdate4 : List (String × String × String) :=
  [ ("INDEX.FT.OptionB.concrete-donor-consumption",
      "s3139_baseUnitScaling_available, s3139_baseUnitScaling_baseUnit, s3139_baseUnitScaling_nontrivial, s3139_badTensorPrimeMatch_of_donor, SourceOptionBComplete, sourceOptionBComplete, sourceOptionBComplete_modelM1",
      "S3139OptionBCompleteActual.lean"),
    ("INDEX.FT.route.residual-v4", "routeOpenResidualsV4",
      "S3139RouteResidualUpdateV4Actual.lean"),
    ("INDEX.PIN.correction-14041", "currentFrozenPin, supersededPinSize, pin_corrected",
      "S3139PinCorrectionActual.lean"),
    ("INDEX.REUSE.OptionB-audit", "optionBPriorArt",
      "S3139PriorArtAudit3Actual.lean") ]

end LeanFormal.IUT.XiFPaper.S3139RouteIdsUpdate4Actual
