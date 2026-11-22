/- P6 hCor312 sandwich 2. -/
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
namespace LeanFormal.IUT.XiFPaper.P6HCor312Sandwich2Actual
universe u v
variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable {V : Type} (I : OriginalInput l V)
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (P : PaperQPilotObjectActual (l := l) (I := I))
theorem p6_hCor312_sandwich2
    (hP6 : actualThetaHullLogRoot (l := l) T ≤ thetaPilotHullLogVolumeReal C3) :
    actualQPilotSignedLogClassical (l := l) T ≤ thetaPilotHullLogVolumeReal C3 :=
  le_trans (actualTargetSigned_actual (l := l) T) hP6
#print axioms p6_hCor312_sandwich2
end LeanFormal.IUT.XiFPaper.P6HCor312Sandwich2Actual
end