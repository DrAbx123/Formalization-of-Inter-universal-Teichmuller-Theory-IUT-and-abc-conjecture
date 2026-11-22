/- Chain of accepted P5 reading inequality and the P7 actual gap (route-valid). -/
import tmp.sheaf.xif.paper.Node09P5ThetaSideFinalActual
import tmp.sheaf.xif.paper.Mzk1P7GapActualActual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import tmp.sheaf.xif.paper.S3133RealifiedQPilotLogVolumeActual
import Mathlib.Tactic
noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1P5P6ReadingChainActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S3133RealifiedQPilotLogVolumeActual
open LeanFormal.IUT.XiFPaper.Node09P5ThetaSideFinalActual
open LeanFormal.IUT.XiFPaper.Mzk1P7GapActualActual

variable {l : PrimeGeFive} (X : N8NativeInput l)
variable [Fintype (Bad (nativePlaceSelection X.S))]
variable [∀ b : Bad (nativePlaceSelection X.S), MeasurableSpace (qVFamTensorBlock X.S b)]
variable [∀ b : Bad (nativePlaceSelection X.S), BorelSpace (qVFamTensorBlock X.S b)]

theorem p5Reading_le : qPilotRealifiedLogVolume X ≤ qVFamThetaReading X :=
  qPilotRealifiedLogVolume_le_thetaReading X
theorem p5Reading_gap : 0 ≤ qVFamThetaReading X - qPilotRealifiedLogVolume X :=
  p7_gap_nonneg_actual X
#print axioms p5Reading_le
#print axioms p5Reading_gap
end LeanFormal.IUT.XiFPaper.Mzk1P5P6ReadingChainActual
end
