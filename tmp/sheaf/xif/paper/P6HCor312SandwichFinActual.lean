/- P6 hCor312 sandwich final. -/
import tmp.sheaf.xif.paper.Mzk1ActualHullTargetMagnitudeActual
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
namespace LeanFormal.IUT.XiFPaper.P6HCor312SandwichFinActual
universe u
variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
theorem p6_hCor312_sandwich_fin :
    -actualQPilotMagnitudeClassical (l := l) T ≤ actualThetaHullLogRoot (l := l) T :=
  by simpa [actualQPilotSignedLogClassical] using actualTargetSigned_actual (l := l) T
#print axioms p6_hCor312_sandwich_fin
end LeanFormal.IUT.XiFPaper.P6HCor312SandwichFinActual
end