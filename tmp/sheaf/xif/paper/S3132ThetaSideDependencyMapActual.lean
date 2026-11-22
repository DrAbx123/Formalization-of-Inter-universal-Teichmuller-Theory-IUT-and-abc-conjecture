set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Paper-route Theta side: dependency map record

Machine-checkable dependency map of the paper-route Theta side after the three
integration batches.  Each node names its file/declaration and its consumer; the
map is data, the correctness is in the cited checker-verified files.

Nodes (in order):
N0  concrete Gaussian arithmetic: concreteGaussianInitialThetaArithmeticData l;
N1  minimal source-clause data: LGPModelSourceClauseMissing l (stage4) =
    signQuotient : SourceSignQuotientData (concrete...) + assembly :
    SourceClauseAssembly ... signQuotient;
N2  native initial-Theta datum: lgpModelNativeData M (stage4);
N3  concrete Haar family: lgpNativeHaarFamily T (stage4), normalization free;
N4  normalization factor CLOSED: S3132ConcreteSourceNormalizationClosureActual
    (factor = 0 via unit-reference mass 1);
N5  sharp residual identity: ThetaSideSharpResidual
    (sourceVFormLogVolume = S3131CanonicalRootedHC T mu);
N6  canonical packaged source readout: thetaSideSharpResidual_canonicalReadout;
N7  comparison-region payload: AdaptedCorollary312ComparisonData via
    modelComparisonData/clauseComparisonData (thetaPilot.value = canonical value);
N8  subsingleton evaluation: clauseThetaValue_of_subsingleton
    (= weight * rooted tensor V-form on a one-point bad family).
-/

namespace LeanFormal.IUT.XiFPaper.S3132ThetaSideDependencyMapActual

/-- A node of the paper-route Theta-side dependency map. -/
structure ThetaSideNode where
  id : String
  declaration : String
  file : String
  consumer : String

/-- The dependency map of the paper-route Theta side. -/
def thetaSideDependencyMap : List ThetaSideNode :=
  [ { id := "N0", declaration := "concreteGaussianInitialThetaArithmeticData l",
      file := "LeanFormal/IUT/IUTI/InitialTheta/ConcreteFinitePlaceBoundary.lean",
      consumer := "N1 arithmetic" }
  , { id := "N1", declaration := "LGPModelSourceClauseMissing",
      file := "S3136ModelSourceClauseActual", consumer := "N2" }
  , { id := "N2", declaration := "lgpModelNativeData",
      file := "S3136ModelSourceClauseActual", consumer := "N3, N5" }
  , { id := "N3", declaration := "lgpNativeHaarFamily",
      file := "S3136NativeHaarFamilyActual", consumer := "N5, N8" }
  , { id := "N4", declaration := "sourceThetaNormalizationFactor_eq_zero",
      file := "S3132ConcreteSourceNormalizationClosureActual", consumer := "N6" }
  , { id := "N5", declaration := "ThetaSideSharpResidual",
      file := "S3132ThetaSideSharpResidualActual", consumer := "N6" }
  , { id := "N6", declaration := "thetaSideSharpResidual_canonicalReadout",
      file := "S3132ThetaSideSharpResidualActual", consumer := "N7" }
  , { id := "N7", declaration := "AdaptedCorollary312ComparisonData",
      file := "S3132ThetaSideModelComparisonDataActual", consumer := "paper-route V2 comparisonRegion" }
  , { id := "N8", declaration := "clauseThetaValue_of_subsingleton",
      file := "S3132ThetaSideSubsingletonComparisonActual", consumer := "N7 evaluation" } ]

/-- The map has nine nodes. -/
theorem thetaSideDependencyMap_length : thetaSideDependencyMap.length = 9 := rfl

/-- Node ids in map order. -/
def thetaSideNodeIds : List String :=
  thetaSideDependencyMap.map (fun n => n.id)

/-- The node id list is N0..N8. -/
theorem thetaSideNodeIds_eq :
    thetaSideNodeIds =
      ["N0", "N1", "N2", "N3", "N4", "N5", "N6", "N7", "N8"] := rfl

#check ThetaSideNode
#check thetaSideDependencyMap
#check thetaSideDependencyMap_length
#check thetaSideNodeIds_eq

end LeanFormal.IUT.XiFPaper.S3132ThetaSideDependencyMapActual