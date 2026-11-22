/-!
# S3139: V2 route residual list (data only; registry frozen except approved re-pins)

The explicit V2 route residuals after the C3 closure, per mainline FINAL-STATUS
A22 and abc's honesty flag.

* FT.route.comparison-invariance (mainline name):
  S3131RouteComparisonInvarianceHypothesis (W) (phi := C3 comparison)
  := forall S, W.logVolume (phi '' S) = W.logVolume S.
* FT.route.measure-invariance (abc name, equivalent wording):
  S3135ComparisonMeasureInvariance := Haar/log-volume of the C3 automorphism
  image of a measurable set equals the volume (paper III Prop 3.9(i) /
  Remark 3.9.5(i) normalization input).
* Affected V2 fields: Cor312ToABCBridgeInterfaceV2.comparisonRegion membership
  lemmas feeding height_le_comparisonRegionVolume, and
  regionVolume_le_normalizedWeight + height/volume dictionary -- these must be
  stated on comparison-invariant source-side data or with the invariance
  hypothesis passed explicitly.
* M0 same-C (mainline R1), M1 place selection + capsule-label link (qpilot),
  stage4 unit map (stage4), fourth-triangle arithmetic inputs (shehdd) remain.
* Not affected: abc's S3135ModelHaar_scaling_image_eq (pure set equality for
  unit scalar action; no C3 comparison involved).

**Component, not paper object.**  No sorry/axiom/True/PUnit/toy carrier (data file).
-/

namespace LeanFormal.IUT.XiFPaper.S3139V2ResidualListActual

/-- One V2 route residual entry. -/
structure V2ResidualEntry where
  id : String
  name : String
  wording : String
  owner : String

/-- The V2 route residual list after the C3 closure. -/
def v2RouteResiduals : List V2ResidualEntry :=
  [ { id := "FT.route.comparison-invariance",
      name := "S3131RouteComparisonInvarianceHypothesis (W) (phi := C3 comparison)",
      wording := "forall S, W.logVolume (phi '' S) = W.logVolume S",
      owner := "mainline" },
    { id := "FT.route.measure-invariance",
      name := "S3135ComparisonMeasureInvariance",
      wording := "Haar/log-volume of the C3 automorphism image of a measurable set = volume (III Prop 3.9(i)/Remark 3.9.5(i) normalization input)",
      owner := "mainline/abc" },
    { id := "FT.M0.same-C",
      name := "same-C identification F ~ F_mod",
      wording := "R1 same-C cross-carrier model identification", owner := "mainline" },
    { id := "FT.M1.place-selection",
      name := "S3133M1ContractSeparatedMissing / S3133M1Remaining (+ capsule-label link)",
      wording := "index equivalence + place agreement; contract-separated label link", owner := "qpilot" },
    { id := "FT.stage4.unit-map",
      name := "S3136LGPGlobalUnitsToLocalUnitsActual.lgpGlobalUnitsToLocalUnits",
      wording := "canonical global-units-to-local-units map", owner := "stage4" },
    { id := "FT.fourth-triangle.inputs",
      name := "signed Theta-hull value + (xi-f) inclusion",
      wording := "fourth-triangle arithmetic inputs", owner := "shehdd route" } ]

end LeanFormal.IUT.XiFPaper.S3139V2ResidualListActual
