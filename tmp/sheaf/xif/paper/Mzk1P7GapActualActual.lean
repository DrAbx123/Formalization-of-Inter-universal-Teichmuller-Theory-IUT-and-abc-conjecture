/- P7 actual gap/margin from the accepted P5 node: the actual qPilot scalar is
at most the actual theta-side reading (Node09P5ThetaSideFinalActual). -/
import tmp.sheaf.xif.paper.Node09P5ThetaSideFinalActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P7GapActualActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.XiFPaper.Node09P5HullInequalityFinalActual
open LeanFormal.IUT.XiFPaper.Node09P5NormalizedRegionActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientBridgeActual
open LeanFormal.IUT.XiFPaper.S3133RealifiedQPilotLogVolumeActual
open LeanFormal.IUT.XiFPaper.Node09P5ReadingBridgeActual
open LeanFormal.IUT.XiFPaper.Mzk1P0QVFamNormBridgeDonorActual
open LeanFormal.IUT.XiFPaper.GlobalQVFamThetaHullScalarActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.Node09P5ThetaSideFinalActual

variable {l : PrimeGeFive} (X : N8NativeInput l)
variable [Fintype (Bad (nativePlaceSelection X.S))]
variable [∀ b : Bad (nativePlaceSelection X.S), MeasurableSpace (qVFamTensorBlock X.S b)]
variable [∀ b : Bad (nativePlaceSelection X.S), BorelSpace (qVFamTensorBlock X.S b)]

/-- Actual P7 gap: the theta-side reading minus the actual qPilot scalar is
nonnegative, from the accepted P5 node inequality. -/
theorem p7_gap_nonneg_actual :
    0 ≤ LeanFormal.IUT.XiFPaper.Node09P5ThetaSideFinalActual.qVFamThetaReading X - LeanFormal.IUT.XiFPaper.S3133RealifiedQPilotLogVolumeActual.qPilotRealifiedLogVolume X :=
  sub_nonneg.mpr (LeanFormal.IUT.XiFPaper.Node09P5ThetaSideFinalActual.qPilotRealifiedLogVolume_le_thetaReading X)

/-- Actual P7 gap decomposition: qPilot plus the gap equals the theta-side
reading. -/
theorem p7_gap_add_actual :
    LeanFormal.IUT.XiFPaper.S3133RealifiedQPilotLogVolumeActual.qPilotRealifiedLogVolume X +
      (LeanFormal.IUT.XiFPaper.Node09P5ThetaSideFinalActual.qVFamThetaReading X - LeanFormal.IUT.XiFPaper.S3133RealifiedQPilotLogVolumeActual.qPilotRealifiedLogVolume X) = LeanFormal.IUT.XiFPaper.Node09P5ThetaSideFinalActual.qVFamThetaReading X :=
  add_sub_cancel (LeanFormal.IUT.XiFPaper.S3133RealifiedQPilotLogVolumeActual.qPilotRealifiedLogVolume X) (LeanFormal.IUT.XiFPaper.Node09P5ThetaSideFinalActual.qVFamThetaReading X)

#print axioms p7_gap_nonneg_actual
#print axioms p7_gap_add_actual

end LeanFormal.IUT.XiFPaper.Mzk1P7GapActualActual
end
