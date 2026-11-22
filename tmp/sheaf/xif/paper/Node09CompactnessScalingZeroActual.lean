/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.S3135ScalingNormalizationActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.OModuleCompactnessLayer
import Mathlib.Tactic
/-! # Card (2) under canonical compactness data: scaling = 1 => log-degree 0 -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Node09CompactnessScalingZeroActual
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3135ScalingNormalizationActual
variable {l : PrimeGeFive} {V : Type}
variable (I : OriginalInput l V) (v : V) (R : I.SourceImageRealization v)
variable (n : ThetaPilotCarrier l) (C : I.SourceOneCircUCompactness v R n)
/-- The canonical compactness Haar data has scaling log-degree zero. -/
theorem scalingLogDegreeZero_sourceOModuleCompactness_haarData :
    S3135ScalingLogDegreeZero I v R n
      (I.sourceOModuleCompactness_haarData v R n C) := by
  unfold S3135ScalingLogDegreeZero
  rw [sourceOModuleCompactness_haarData_scaling]
  exact I.sourceLocalLogDegree_one v
#check scalingLogDegreeZero_sourceOModuleCompactness_haarData
end LeanFormal.IUT.XiFPaper.Node09CompactnessScalingZeroActual
end