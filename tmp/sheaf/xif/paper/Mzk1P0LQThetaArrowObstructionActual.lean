/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P0LNormalizationJointActual
import tmp.sheaf.xif.paper.Mzk1P0LNormalizationExplicitActual
import tmp.sheaf.xif.paper.Mzk1P0LReadoutLogActual
import Mathlib.Tactic
/-! # LQThetaSourceArrow obstruction in the theta-nonnegative branch -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0LQThetaArrowObstructionActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.Mzk1P0LPaperInstanceActual
open LeanFormal.IUT.XiFPaper.Mzk1P0LNormalizationActual
open LeanFormal.IUT.XiFPaper.Mzk1P0LNormalizationExplicitActual
open LeanFormal.IUT.XiFPaper.Mzk1P0LNormalizationJointActual
open LeanFormal.IUT.XiFPaper.Mzk1P0LReadoutLogActual
variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)
/-- In the theta-nonnegative branch, the L q/theta source arrow is empty:
its normalization_eq would force lThetaNormFactor = 0, contradicting
lThetaNormFactor > theta >= 0. -/
theorem lQThetaSourceArrow_isEmpty_of_theta_nonneg
    (h : 0 ≤ thetaReadActual I place) : IsEmpty (LQThetaSourceArrow I place) := by
  refine ⟨fun A => ?_⟩
  have hnorm : thetaReadActual I place = Real.log ‖(C3LAt I place).q.q‖ :=
    A.normalization_eq
  have hqread : qReadActual I place = Real.log ‖(C3LAt I place).q.q‖ :=
    qReadActual_eq_logNorm I place
  have hfactor : lThetaNormFactor I place = 0 := by
    rw [lThetaNormFactor_eq_theta_sub_qRead, hnorm, hqread]
    ring
  have hgt := lThetaNormFactor_gt_theta_of_theta_nonneg I place h
  rw [hfactor] at hgt
  linarith
/-- Exact remaining fields if one insists on the arrow for theta < 0. -/
def lQThetaArrowGapFields : List String :=
  [ "q_mem_thetaRegion: requires qComponentMemGap (q in every local log-shell)",
    "CommonPrimeNormInstanceCompat for the q component fiber norm",
    "normalization_eq: thetaReadActual = Real.log||q.q||; in theta>=0 branch it is impossible",
    "theta<0 branch still requires the exact normalization identity" ]
theorem lQThetaArrowGapFields_length : lQThetaArrowGapFields.length = 4 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1P0LQThetaArrowObstructionActual
end