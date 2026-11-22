import tmp.sheaf.xif.paper.S3132SourceAdaptedCorollary312DataActual
import tmp.sheaf.xif.paper.S3132ConcreteSourceVFormInstantiatedActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1500000

noncomputable section
open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S3131CanonicalRootedQCActual
open LeanFormal.IUT.XiFPaper.S3129IQHullLogVolumeSourceActual
open LeanFormal.IUT.XiFPaper.S3132IQHullRealLogVolumeReadoutActual
open LeanFormal.IUT.XiFPaper.S3132ConcreteSourceNormalizationClosureActual
open LeanFormal.IUT.XiFPaper.S3132ConcreteSourceCanonicalResidualActual
open LeanFormal.IUT.XiFPaper.S3136NativeHaarFamilyActual
open LeanFormal.IUT.XiFPaper.S3136ConcreteExample36NativeDataActual
open LeanFormal.IUT.XiFPaper.S3132ConcreteSourceVFormInstantiatedActual
open LeanFormal.IUT.XiFPaper.S3132SourceAdaptedPilotComparisonActual
open LeanFormal.IUT.XiFPaper.S3132SourceAdaptedCorollary312DataActual

namespace LeanFormal.IUT.XiFPaper.S3132ThetaSideReadoutComparisonDataActual

/-! # Paper-route Theta side: comparison-region data from the concrete readout

Wires the concrete Example 3.6 Theta-side readout (canonical rooted value
`S3131CanonicalRootedHC T mu` under the data + V-form residual) into the
source-adapted Corollary 3.12 comparison payload
`AdaptedCorollary312ComparisonData` (the paper-route comparison-region data
shape, adapted from vendor CorollarySchema).  The signed Theta payload is the
negative of the positive-magnitude canonical readout; the q-side comparison is
an explicit hypothesis (the R1/q-side work of the other streams).
Component, not a paper object; owner hull. -/

/-- Comparison-region payload with an arbitrary Theta-side positive magnitude. -/
def comparisonDataOfMagnitudes (thetaH qSigned : ℝ) (hq : 0 < -qSigned)
    (hle : qSigned ≤ -thetaH) : AdaptedCorollary312ComparisonData :=
  { thetaSigned := -thetaH
    qSigned := qSigned
    q_positive := hq
    qSigned_le_thetaSigned := hle }

/-- The adapted `thetaPilot` stored value is the positive-magnitude Theta readout. -/
theorem comparisonDataOfMagnitudes_thetaPilot_value
    (thetaH qSigned : ℝ) (hq : 0 < -qSigned) (hle : qSigned ≤ -thetaH) :
    (comparisonDataOfMagnitudes thetaH qSigned hq hle).thetaPilot.value = thetaH := by
  simp [comparisonDataOfMagnitudes, AdaptedCorollary312ComparisonData.thetaPilot,
    adaptedSignedPilotLogVolume]

/-- The adapted `qPilot` stored value is the positive q magnitude. -/
theorem comparisonDataOfMagnitudes_qPilot_value
    (thetaH qSigned : ℝ) (hq : 0 < -qSigned) (hle : qSigned ≤ -thetaH) :
    (comparisonDataOfMagnitudes thetaH qSigned hq hle).qPilot.value = -qSigned := by
  simp [comparisonDataOfMagnitudes, AdaptedCorollary312ComparisonData.qPilot,
    adaptedSignedPilotLogVolume]

/-- The comparison-region payload from the concrete Example 3.6 Theta readout
(canonical rooted value), conditional on the remaining data + V-form residual. -/
def comparisonDataOfConcreteReadout
    (M : LGPConcreteExample36NativeDataMissing l)
    [Fintype (Bad (nativePlaceSelection (lgpConcreteExample36NativeData M)))]
    (h : MissingConcreteExample36VFormCanonicalReadout (l := l) M)
    (qSigned : ℝ) (hq : 0 < -qSigned)
    (hle : qSigned ≤
      -S3131CanonicalRootedHC (l := l)
        (lgpConcreteExample36NativeData M)
        (lgpNativeHaarFamily (lgpConcreteExample36NativeData M))) :
    AdaptedCorollary312ComparisonData :=
  comparisonDataOfMagnitudes
    (S3131CanonicalRootedHC (l := l)
      (lgpConcreteExample36NativeData M)
      (lgpNativeHaarFamily (lgpConcreteExample36NativeData M))) qSigned hq hle

/-- The concrete-readout payload has the canonical rooted value as its Theta
pilot magnitude. -/
theorem comparisonDataOfConcreteReadout_thetaPilot_value
    (M : LGPConcreteExample36NativeDataMissing l)
    [Fintype (Bad (nativePlaceSelection (lgpConcreteExample36NativeData M)))]
    (h : MissingConcreteExample36VFormCanonicalReadout (l := l) M)
    (qSigned : ℝ) (hq : 0 < -qSigned)
    (hle : qSigned ≤
      -S3131CanonicalRootedHC (l := l)
        (lgpConcreteExample36NativeData M)
        (lgpNativeHaarFamily (lgpConcreteExample36NativeData M))) :
    (comparisonDataOfConcreteReadout (l := l) M h qSigned hq hle).thetaPilot.value =
      S3131CanonicalRootedHC (l := l)
        (lgpConcreteExample36NativeData M)
        (lgpNativeHaarFamily (lgpConcreteExample36NativeData M)) :=
  comparisonDataOfMagnitudes_thetaPilot_value _ _ hq hle

#check comparisonDataOfMagnitudes
#check comparisonDataOfMagnitudes_thetaPilot_value
#check comparisonDataOfConcreteReadout
#check comparisonDataOfConcreteReadout_thetaPilot_value

end LeanFormal.IUT.XiFPaper.S3132ThetaSideReadoutComparisonDataActual
end
