/- P6 H_theta normalization: the actual q-pilot signed log is -M and is at most H_theta. -/
import tmp.sheaf.xif.paper.Mzk1ActualHullTargetMagnitudeActual
import Mathlib.Tactic
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetActual
open LeanFormal.IUT.XiFPaper.Mzk1ActualHullTargetMagnitudeActual
namespace LeanFormal.IUT.XiFPaper.P6HThetaNormalizationActual
universe u
variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [hMeas : ∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [hBorel : ∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
include T hMeas hBorel
/-- Original normalization: q-pilot signed log = -M, where M is the actual
q-pilot magnitude; and -M ≤ H_theta from the accepted P5 hull target. -/
theorem p6_neg_M_le_HTheta :
    -actualQPilotMagnitudeClassical (l := l) T ≤ actualThetaHullLogRoot (l := l) T := by
  simpa [actualQPilotSignedLogClassical] using actualTargetSigned_actual (l := l) T
#print axioms p6_neg_M_le_HTheta
end LeanFormal.IUT.XiFPaper.P6HThetaNormalizationActual
end