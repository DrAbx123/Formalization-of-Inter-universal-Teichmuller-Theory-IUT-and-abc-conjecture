/- P6 H_theta upper sandwich: -M <= H_theta <= H_target. -/
import tmp.sheaf.xif.paper.Mzk1ActualHullTargetMagnitudeActual
import tmp.sheaf.xif.paper.Mzk1ActualReadingTargetActual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import Mathlib.Tactic
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1ActualHullTargetMagnitudeActual
open LeanFormal.IUT.XiFPaper.Mzk1ActualReadingTargetActual
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
namespace LeanFormal.IUT.XiFPaper.P6HThetaUpperSandwichActual
universe u v
variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable {V : Type} (I : OriginalInput l V)
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (P : PaperQPilotObjectActual (l := l) (I := I))
theorem p6_hTheta_upper_sandwich
    (hP6 : actualThetaHullLogRoot (l := l) T ≤ thetaPilotHullLogVolumeReal C3) :
    (-actualQPilotMagnitudeClassical (l := l) T ≤ actualThetaHullLogRoot (l := l) T) ∧
      actualQPilotSignedLogClassical (l := l) T ≤ thetaPilotHullLogVolumeReal C3 :=
  ⟨by simpa [actualQPilotSignedLogClassical, ActualPaperXiFTarget] using actualTargetSigned_actual (l := l) T,
    le_trans (actualTargetSigned_actual (l := l) T) hP6⟩
#print axioms p6_hTheta_upper_sandwich
end LeanFormal.IUT.XiFPaper.P6HThetaUpperSandwichActual
end