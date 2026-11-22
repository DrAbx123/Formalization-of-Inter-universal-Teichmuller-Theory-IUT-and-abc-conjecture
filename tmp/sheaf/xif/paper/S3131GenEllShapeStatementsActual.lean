import LeanFormal.IUT.Audit.Status

/-! # S3131 GenEll-shape statement set + dependency analysis (data only) -/

namespace LeanFormal.IUT.XiFPaper.S3131GenEllShapeStatementsActual

/-- Vendor lines that record the IUT IV / GenEll function-level relations. -/
def S3131GenEllVendorAnchors : List (String × String) :=
  [ ("Iut/Stage1/IUTStage1IUTIVAlgebra.lean", "hullSystem.logVolume of logUnitsRegion (1956-1958), shiftedTensorRegion (1959-1961), tensorContainerRegion (2114-2144)"),
    ("Iut/SourceTrace/IUTIVPaperLedger.lean:176", "GenEll transfer is an EXPLICIT HYPOTHESIS (honesty ledger) - not a proved theorem"),
    ("Iut/SourceTrace/Corollary312SourceGraph.lean:126,162,223", "qPilotAnalyticAcceptance/CorridorAcceptance records (stored determinant/comparison/arithmetic degree)") ]

/-- Dependency analysis: which parts are provable now vs GenEll-strength. -/
def S3131GenEllDependencyAnalysis : List (String × String) :=
  [ ("(a) comparisonRegion/logShellPoint/membership", "PROVABLE NOW: S3131PaperRouteSkeletonActual.comparisonOfResiduals"),
    ("(b) dilation (1+eps)", "PROVABLE NOW: heightComparisonFamily_of_undilated (nonneg log-volume bookkeeping)"),
    ("(c) dilation (1+eps)", "PROVABLE NOW: regionVolumeFamily_of_undilated (arithmeticWeight >= 0 bookkeeping)"),
    ("(b) UNDILATED height/dictionary bound", "PAPER DATA: needs hull canonical readout + sourceLocalLogDegree dictionary files; feeds MissingConcreteVFormCanonicalReadout"),
    ("(c) UNDILATED arithmetic strength bound", "GENELL STRENGTH: IV section 2 estimate, explicit hypothesis in vendor ledger, NOT formalized in tree") ]

theorem S3131GenEllVendorAnchors_length : S3131GenEllVendorAnchors.length = 3 := rfl
theorem S3131GenEllDependencyAnalysis_length : S3131GenEllDependencyAnalysis.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.S3131GenEllShapeStatementsActual