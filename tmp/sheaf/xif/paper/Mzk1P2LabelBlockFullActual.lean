/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P2LabelBlockCompleteActual
open LeanFormal.IUT.XiFPaper.Mzk1P2LabelBlockCompleteActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionFieldScalingActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open scoped BigOperators ENNReal

open LeanFormal.IUT.XiFPaper.Mzk1P2LabelBlockCoefficientActual

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction.Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection T))]

theorem p2FullLabelBlock_sources (A : P2ActualLabelBlock T) :
    p2BlockSourceQ T A = rootThetaFieldLambda T A.b * p2Coefficient T A.b
      ∧ p2BlockLanding T A = p2BlockSourceTheta T A
      ∧ p2BlockWeight T A = Module.finrank ℚ_[qVFamTensorP T A.b] (rootNormedExtension T A.b) :=
  p2Block_four_sources T A

end
