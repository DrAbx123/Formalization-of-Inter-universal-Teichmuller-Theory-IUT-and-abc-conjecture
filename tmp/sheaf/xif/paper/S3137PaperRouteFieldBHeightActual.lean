import LeanFormal.IUT.Audit.Status

/-! # S3137: paper-route field (b) height — REUSE record

INDEX.PAPER-ROUTE.height-comparison (class B paper-proved formalization target)
is reduced by the tree's additive height-weight theorem; the concrete model
consumer exists in IQCarrierConcreteModel.  This file records the exact reuse
points (no new definitions, no re-proving).
-/

namespace LeanFormal.IUT.XiFPaper.S3137PaperRouteFieldBHeightActual

/-- Reuse points for paper-route field (b). -/
def S3137PaperRouteFieldBReuse : List (String × String × String) :=
  [ ("additive height/weight reduction", "LeanFormal/IUT/ABCBridge/Geometry/ThetaBoundToHeightWeight.lean:67 heightWeightBound_of_normalizedVolumeComparison", "REUSE: converts normalized volume comparison into the additive height bound"),
    ("V2 additive bound contract", "ABCHeightArithmeticWeightComparison.ABCHeightWeightAdditiveBoundV2 (approved additive re-freeze)", "REUSE: paper-faithful (b) shape"),
    ("bridge height bound", "Cor312ToABCBridgeInterface.lean:426 cor312ToABCBridge_heightBound", "REUSE"),
    ("concrete model comparison instance", "IQCarrierConcreteModel.lean:413/431 iqCarrierModel_epsilonComparison / iqCarrierModel_epsilonComparisonAdditive", "REUSE: actual concrete instance feeding the reduction"),
    ("concrete model logShellPoint", "IQCarrierConcreteModel.lean:230 iqCarrierModelLogShellPoint", "REUSE: named datum for the concrete model; paper logShellPoint still class B input"),
    ("uniform V1 form", "Cor312ComparisonGapReduction.lean:232/272 cor312Gap1_exists_carrier_arithmeticWeight_gt_normalizedComparisonRegionVolume / cor312Gap1_not_forall_...", "NEGATIVE: uniform V1 refuted; do not use") ]

theorem S3137PaperRouteFieldBReuse_length :
    S3137PaperRouteFieldBReuse.length = 6 := rfl

end LeanFormal.IUT.XiFPaper.S3137PaperRouteFieldBHeightActual

namespace LeanFormal.IUT.Audit

/-- INDEX note: paper-route field (b) reuse. -/
def S3137PaperRouteFieldBRecord : Obligation :=
  { id := "INDEX.PAPER-ROUTE.height-comparison-reuse"
    source := "ThetaBoundToHeightWeight.lean:67; ABCHeightArithmeticWeightComparison; Cor312ToABCBridgeInterface:426; IQCarrierConcreteModel:413/431; Cor312ComparisonGapReduction:232/272"
    status := VerificationStatus.interface
    note := "FIELD (b) REUSE: heightWeightBound_of_normalizedVolumeComparison (ThetaBoundToHeightWeight:67) is the tree reduction from normalized volume comparison to the additive ABC height bound; ABCHeightWeightAdditiveBoundV2 is the paper-faithful shape; cor312ToABCBridge_heightBound consumes it; IQCarrierConcreteModel provides an ACTUAL concrete comparison instance (epsilonComparison/Additive) and named logShellPoint. Uniform V1 form is REFUTED (counterexample theorems). Remaining paper input: logShellPoint as an actual paper object + nontrivial dictionary/point bound (class B); NOT ABC-strength here."
    dependsOn := ["S3137PaperRouteFieldBHeightActual", "INDEX.PRIOR-ART.paper-route"] }

end LeanFormal.IUT.Audit
