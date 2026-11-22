import tmp.sheaf.xif.paper.S1414NormalizedReadoutActual
import tmp.sheaf.xif.paper.S1446ReportCReadoutActual
import tmp.sheaf.xif.paper.S1475ReportCExactInputsActual
import tmp.sheaf.xif.paper.S1095PushforwardHullEqActual

/-! # S1649: Route C source readout transport by the intrinsic image measure

S1414's source readout is the degree-normalized relative Haar readout of
`qPilotQ1URegion` against the canonical unit reference in the qVFam tensor
block.  This file transports it to the root-stack image using the *intrinsic*
pushforward measure of the actual embedding, not ambient Haar.  It also records
the exact missing source identification: the tree has no proof that this qVFam
normalized log-volume is the paper's source-prescribed readout (the qVFam
coefficient world and the source q readout are not identified).

No ambient Haar = pushforward and no lattice inclusion is used as the source
readout. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S1649RouteCReadoutActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S1414NormalizedReadoutActual
open LeanFormal.IUT.XiFPaper.S1446ReportCReadoutActual
open LeanFormal.IUT.XiFPaper.S1475ReportCExactInputsActual
open LeanFormal.IUT.XiFPaper.S1095PushforwardHullEqActual
open LeanFormal.IUT.XiFPaper.S1072CanonicalQ1URegionActual
open LeanFormal.IUT.XiFPaper.S1073RootStackPaperThetaHullActual
open LeanFormal.IUT.XiFPaper.S782FiniteRootStackExtensionActual
open LeanFormal.IUT.XiFPaper.S312QPilotRootTensorBaseChangeActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.S839PaperRootMinimalProductCompactActual
open LeanFormal.IUT.XiFPaper.S841FractionalCompactAbsorptionActual
open LeanFormal.IUT.XiFPaper.S1086PerBQ1URootHullActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- The intrinsic image measure on the root-stack extension: the pushforward
of the qVFam Haar along the actual root-stack embedding.  This is the measure
used by the source if it reads the image intrinsically; no ambient Haar is
asserted to equal it. -/
noncomputable def s1649IntrinsicImageMeasure :
    Measure (rootStackExtension (l := l) T b) :=
  Measure.map (rootStackEmbedding (l := l) T b)
    (Measure.addHaar : Measure (qVFamTensorBlock T b))

/-- The source region transported to the root-stack image. -/
noncomputable def s1649SourceRegionImage : Set (rootStackExtension (l := l) T b) :=
  rootStackEmbedding (l := l) T b '' qPilotQ1URegion (l := l) T b

/-- The reference region transported to the root-stack image. -/
noncomputable def s1649ReferenceRegionImage : Set (rootStackExtension (l := l) T b) :=
  rootStackEmbedding (l := l) T b '' s1414SourceReference T b

/-- **Route C transport, intrinsic-measure branch**: on the image, the relative
normalized readout for the image measure equals the source qVFam readout.  The
reference region is transported by the same embedding, so this is not an
ambient-Haar identity. -/
theorem s1649IntrinsicReadout_eq_sourceReadout :
    s1446RelativeReadout (s1649IntrinsicImageMeasure T b)
        (s1649SourceRegionImage T b) (s1649ReferenceRegionImage T b) =
      s1414RelativeReadout (Measure.addHaar : Measure (qVFamTensorBlock T b))
        (qPilotQ1URegion (l := l) T b) (s1414SourceReference T b) := by
  unfold s1649IntrinsicImageMeasure s1649SourceRegionImage s1649ReferenceRegionImage
  exact s1446RelativeReadout_intrinsicImage_eq
    (Measure.addHaar : Measure (qVFamTensorBlock T b))
    (s1414Embedding_measurable (l := l) T b)
    (rootStackEmbedding_injective_actual (l := l) T b)
    (by
      have hq := s1475Q1URegionMeasurable_actual (l := l) T b
      unfold S1086Q1URegionMeasurable at hq
      exact hq)
    (by
      simpa [s1414SourceReferenceImage] using
        s1414SourceReferenceImage_measurable (l := l) T b)

/-- The headline source readout is the degree-normalized version of the qVFam
relative readout; this is a definitional identity, and says nothing yet about
the paper source readout. -/
theorem s1649SourceReadout_eq_relativeReadout :
    s1414SourceReadout T b =
      (1 / (Module.finrank ℚ_[qVFamTensorP T b] (qVFamTensorBlock T b) : ℝ)) *
        s1414RelativeReadout (Measure.addHaar : Measure (qVFamTensorBlock T b))
          (qPilotQ1URegion (l := l) T b) (s1414SourceReference T b) := rfl

/-- The intrinsic image readout is exactly the degree-normalized source readout. -/
theorem s1649IntrinsicReadout_eq_sourceReadout_degreeNormalized :
    (1 / (Module.finrank ℚ_[qVFamTensorP T b] (qVFamTensorBlock T b) : ℝ)) *
        s1446RelativeReadout (s1649IntrinsicImageMeasure T b)
          (s1649SourceRegionImage T b) (s1649ReferenceRegionImage T b) =
      s1414SourceReadout T b := by
  rw [s1649IntrinsicReadout_eq_sourceReadout, ← s1649SourceReadout_eq_relativeReadout]

/-- The qVFam source readout object is exactly the normalized log-volume of
`qPilotQ1URegion` in the qVFam tensor block.  This is actual, but it is not yet
the paper source readout. -/
theorem s1649SourceReadout_eq_normalizedLogVolume :
    s1414SourceReadout T b =
      arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple
        (Measure.addHaar : Measure (qVFamTensorBlock T b))
        (qPilotQ1URegion (l := l) T b) :=
  s1414SourceReadout_eq_normalizedLogVolume (l := l) T b

#check s1649IntrinsicImageMeasure
#check s1649IntrinsicReadout_eq_sourceReadout
#check s1649IntrinsicReadout_eq_sourceReadout_degreeNormalized
#check s1649SourceReadout_eq_normalizedLogVolume

end LeanFormal.IUT.XiFPaper.S1649RouteCReadoutActual
end
