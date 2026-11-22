import tmp.sheaf.xif.paper.S1414NormalizedReadoutActual
import tmp.sheaf.xif.paper.S1579OLeFractionalZeroAnalysisActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1652OriginalInequalityStatementActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open MeasureTheory
open LeanFormal.IUT.XiFPaper.S1414NormalizedReadoutActual
open LeanFormal.IUT.XiFPaper.S1414NormalizedReadoutActual
open LeanFormal.IUT.XiFPaper.S1086PerBQ1URootHullActual
open LeanFormal.IUT.XiFPaper.S839PaperRootMinimalProductCompactActual
open LeanFormal.IUT.XiFPaper.S853OInFZeroAbsorptionActual
open LeanFormal.IUT.XiFPaper.S841FractionalCompactAbsorptionActual
open LeanFormal.IUT.XiFPaper.S1579OLeFractionalZeroAnalysisActual
open LeanFormal.IUT.XiFPaper.S1072CanonicalQ1URegionActual
open LeanFormal.IUT.XiFPaper.S1085PushforwardHullEqActual
open LeanFormal.IUT.XiFPaper.S1080PushforwardConstructionActual
open LeanFormal.IUT.XiFPaper.S1082LambdaOPositivityExactActual
open LeanFormal.IUT.XiFPaper.S793PaperLeastLambdaOHullActual
open LeanFormal.IUT.XiFPaper.S1073RootStackPaperThetaHullActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-! ## 1. The original Route C/F readout inequality object -/

/-- The original per-b readout inequality of Route C/F: the actual source
readout is bounded by the actual theta-side hull readout.  Domain: the fixed
source data T and the bad place b.  Direction: <=.  This is a real-number
inequality of the two actual readouts, not a lattice inclusion. -/
def S1652OriginalReadoutInequality : Prop :=
  s1414SourceReadout T b ≤ s1414HullReadout T b

/-- The original source readout (actual object). -/
noncomputable abbrev S1652SourceReadout : ℝ :=
  s1414SourceReadout T b

/-- The original theta-side hull readout (actual object). -/
noncomputable abbrev S1652HullReadout : ℝ :=
  s1414HullReadout T b

/-- The source readout object is the degree-normalized relative Haar readout
of qPilotQ1URegion relative to the source reference region. -/
theorem s1652SourceReadout_eq_normalizedLogVolume :
    S1652SourceReadout T b =
      arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple
        (Measure.addHaar : Measure (qVFamTensorBlock T b))
        (qPilotQ1URegion T b) :=
  s1414SourceReadout_eq_normalizedLogVolume T b

/-- The hull readout object is the degree-normalized relative pushforward Haar
readout of the root-stack paper theta hull relative to the source reference
image. -/
theorem s1652HullReadout_eq_hullRegion
    (hinj : S1085EmbeddingInjective T b)
    (hmeas : S1085EmbeddingMeasurable T b)
    (hH : S1414HullImageMeasurable T b) :
    S1652HullReadout T b =
      (1 / (Module.finrank ℚ_[qVFamTensorP T b] (qVFamTensorBlock T b) : ℝ)) *
        (Real.log ((Measure.addHaar : Measure (qVFamTensorBlock T b))
          (paperLambdaORegion T b
            (paperRootCoefficientFamily T b))).toReal -
         Real.log ((Measure.addHaar : Measure (qVFamTensorBlock T b))
          (s1414SourceReference T b)).toReal) :=
  s1414HullReadout_eq_hullRegion T b hinj hmeas hH

/-! ## 2. Downstream consumer -/

/-- The exact source fields of S1414 imply the original readout inequality.
This is the Route C/F consumer; it does not use S841/S853 lattice inclusion. -/
theorem s1652OriginalReadoutInequality_of_exact
    (hcont : S1086Q1UImageContainment T b)
    (hS : S1086Q1URegionMeasurable T b)
    (hFirst : S1414ExactFirstField T b) :
    S1652OriginalReadoutInequality T b :=
  s1414XiFNormalizedReadout_le_of_exact T b hcont hS hFirst

/-- Conditional consumer from the full S1086/S1414 hypotheses. -/
theorem s1652OriginalReadoutInequality_of_inputs
    (hcont : S1086Q1UImageContainment T b)
    (hinj : S1085EmbeddingInjective T b)
    (hmeas : S1085EmbeddingMeasurable T b)
    (hS : S1086Q1URegionMeasurable T b)
    (hH : S1414HullImageMeasurable T b)
    (hQpos : 0 < (Measure.addHaar : Measure (qVFamTensorBlock T b))
      (qPilotQ1URegion T b))
    (hQfin : (Measure.addHaar : Measure (qVFamTensorBlock T b))
      (qPilotQ1URegion T b) < ⊤)
    (hHullFin : s1080PushforwardHaar T b
      (rootStackPaperThetaHull T b) < ⊤) :
    S1652OriginalReadoutInequality T b :=
  s1414XiFNormalizedReadout_le T b hcont hinj hmeas hS hH
    hQpos hQfin hHullFin

/-! ## 3. Lattice inclusion objects are separate auxiliary inputs -/

/-- S841 pointwise absorption.  This is a lattice/product-image statement on
the tensor block, not the original readout inequality. -/
abbrev S1652LatticePointwiseAbsorption : Prop :=
  S841PointwiseAbsorption T b

/-- S853 lattice inclusion O_hol <= F(0).  This is a lattice inclusion on the
tensor block, not the original readout inequality. -/
abbrev S1652LatticeHolomorphicLeZero : Prop :=
  S853OLeFractionalZeroRequired T b

/-- The lattice auxiliary input is not used in the original readout inequality
statement.  This theorem only records the separate consumer of the lattice
input, to prevent mixing the two targets. -/
theorem s1652LatticeInput_consumer
    (h : S1652LatticeHolomorphicLeZero T b) :
    S841PointwiseAbsorption T b :=
  s1579PointwiseAbsorption_of_forward T b h

end LeanFormal.IUT.XiFPaper.S1652OriginalInequalityStatementActual

end
