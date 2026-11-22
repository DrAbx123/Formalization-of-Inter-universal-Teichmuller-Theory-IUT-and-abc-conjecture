/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P2QNativeReadingCorrectedActual
import tmp.sheaf.xif.paper.QVFamNormalizedGeneratorSupplyActual
import tmp.sheaf.xif.paper.QVFamNormalizedCoefficientBridgeActual
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotLogVolume
import Mathlib.Tactic

/-! # A2/P2: norm-instance agreement is exactly the known source condition

This file is **independent of the obsolete P0 donor**. It proves:
* `P2QHatNormStandardAgreement` (normalized norm = default norm, pointwise/global)
  is **exactly** `qVFamNormRatio = 1`, which is the known
  `PaperSourceCorrectionFreeFields.normRatio_one` condition;
* the default/adic-norm q reading `localLogMagnitude = -log(default norm)` is
  unconditional by definition.

It does **not** claim `P2QHatNormInstanceAgreement` (which uses `‖c0QHat‖`)
unconditionally: the probe in `Mzk1P2QHatNormRootBaseActual` showed `c0QHat`
carries the normalized instance while `qVFamDefaultNorm` is the adic instance,
so the bridge is a norm-instance coherence, not a new mathematical gap.
-/

noncomputable section
set_option maxHeartbeats 400000

namespace LeanFormal.IUT.XiFPaper.Mzk1P2QHatNormAgreementUnconditionalActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientBridgeActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open scoped BigOperators ENNReal

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction.Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection T))]

/-- Pointwise norm-instance agreement ↔ ratio one (existing source condition). -/
theorem p2QHatNormStandardAgreement_iff_ratio_one
    (b : LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction.Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection T)) :
    (qVFamNormalizedNorm T b = qVFamDefaultNorm T b) ↔ qVFamNormRatio T b = 1 := by
  unfold qVFamNormRatio
  have hne : qVFamDefaultNorm T b ≠ 0 := by
    unfold qVFamDefaultNorm
    exact norm_ne_zero_iff.mpr (qVFamily T b).q_ne_zero
  constructor
  · intro h
    rw [h, div_self hne]
  · intro h
    exact (div_eq_one_iff_eq hne).mp h

/-- Global norm-instance agreement ↔ all ratios one. -/
theorem p2QHatNormStandardAgreement_iff :
    (∀ b : LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction.Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection T),
        qVFamNormalizedNorm T b = qVFamDefaultNorm T b) ↔
      ∀ b : LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction.Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection T),
        qVFamNormRatio T b = 1 :=
  ⟨fun h b => (p2QHatNormStandardAgreement_iff_ratio_one T b).mp (h b),
   fun h b => (p2QHatNormStandardAgreement_iff_ratio_one T b).mpr (h b)⟩

/-- Default (adic) norm reading: unconditional by the definitions. -/
theorem p2QNativeReading_defaultNorm
    (b : LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction.Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection T)) :
    localLogMagnitude (qVFamily T b) = -Real.log (qVFamDefaultNorm T b) := by
  unfold localLogMagnitude localSignedLog qVFamDefaultNorm
  rfl

end LeanFormal.IUT.XiFPaper.Mzk1P2QHatNormAgreementUnconditionalActual

end