/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.PaperLevelXiFTargetProofActual
import tmp.sheaf.xif.paper.PaperLevelXiFTargetBridgeActual
import tmp.sheaf.xif.paper.BadPlaceProcessionNormalizedComparisonActual
import Mathlib.Tactic
/-! #1 paper 3.12 actual comparison consumer

Paper 3.12 signed comparison on the ACTUAL root theta hull:
  actualQPilotSignedLogClassical <= actualThetaHullLogRoot
This is proved unconditionally in PaperLevelXiFTargetBridgeActual.actualPaperXiFTarget
(root hull measure positivity/finiteness are internal, no hpos/hfin assumptions).

The procession-normalized coefficient comparison in
BadPlaceProcessionNormalizedComparisonActual is the c_norm/(2l) qVFam block MODEL;
its identification with the actual theta hull is the separate Prop
ThetaHullCoefficientScalarBridge (PaperLevelXiFTargetBridgeActual).
-/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0Paper312ComparisonActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetProofActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetBridgeActual
open LeanFormal.IUT.XiFPaper.BadPlaceProcessionNormalizedComparisonActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
/-- Paper 3.12 signed comparison on the actual root theta hull. -/
def Paper312Comparison : Prop := ActualPaperXiFTarget (l := l) T
theorem paper312Comparison_actual : Paper312Comparison T :=
  actualPaperXiFTarget (l := l) T
/-- Magnitude form. -/
theorem paper312Comparison_iff_magnitude :
    Paper312Comparison T ↔ ActualPaperXiFTargetMagnitude (l := l) T := by
  unfold Paper312Comparison
  exact actualPaperXiFTarget_iff_magnitude (l := l) T
/-- Coefficient model bridge: actual theta hull magnitude equals the S13 c_norm sum. -/
def Paper312ModelBridge : Prop := ThetaHullCoefficientScalarBridge (l := l) T
/-- If the coefficient model bridge holds, the actual comparison is the model comparison. -/
theorem paper312Comparison_of_model_bridge (h : Paper312ModelBridge T) :
    ActualPaperXiFTargetMagnitude (l := l) T := by
  have hmodel := processionNormalizedComparison (l := l) T
  rw [processionNormalizedThetaLog_eq_s13,
    processionNormalizedQPilotLog_eq_actual] at hmodel
  unfold Paper312ModelBridge ThetaHullCoefficientScalarBridge at h
  unfold ActualPaperXiFTargetMagnitude actualThetaHullMagnitudeRoot
  unfold actualThetaHullLogRoot
  rw [h]
  simpa [actualQPilotMagnitudeClassical] using hmodel
end LeanFormal.IUT.XiFPaper.Mzk1P0Paper312ComparisonActual
end