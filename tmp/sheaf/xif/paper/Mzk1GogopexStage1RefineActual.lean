/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.gogopex.Iut.Stage1.CorollarySchema

/-! # A515: Stage1 refinement objects (Gogopex Corollary312 data + target chain) -/

noncomputable section

namespace LeanFormal.IUT.Objects.GogopexStage1

open Iut RealLineCopy

/-- A Stage 1 refinement: the Gogopex signed q/Theta comparison data together with an
intermediate target signed value between q and Theta (the three-term chain). -/
structure Stage1Refinement where
  /-- The signed q/Theta comparison data. -/
  comparison : Stage1.Corollary312ComparisonData
  /-- The intermediate target signed log-volume. -/
  targetSigned : Real
  /-- `q <= target`. -/
  q_le_target : comparison.qSigned ≤ targetSigned
  /-- `target <= Theta`. -/
  target_le_theta : targetSigned ≤ comparison.thetaSigned

/-- The three-term chain gives `qSigned <= thetaSigned` (consumer of `le_trans`). -/
theorem Stage1Refinement.q_le_theta (D : Stage1Refinement) :
    D.comparison.qSigned ≤ D.comparison.thetaSigned :=
  le_trans D.q_le_target D.target_le_theta

/-- The refined object still yields the Corollary 3.12 signed inequality (Gogopex). -/
theorem Stage1Refinement.corollary312 (D : Stage1Refinement) :
    Stage1.Corollary312Inequality D.comparison.thetaPilot D.comparison.qPilot :=
  D.comparison.corollary312

/-- The q-pilot stored magnitude is positive (Gogopex projection). -/
theorem Stage1Refinement.qPilot_positive (D : Stage1Refinement) :
    0 < D.comparison.qPilot.value :=
  D.comparison.qPilot_positive

/-- The Stage1 comparison recovered from the refinement is the base data comparison. -/
theorem Stage1Refinement.stage1Comparison_comparison (D : Stage1Refinement) :
    D.comparison.stage1Comparison.comparison = D.comparison.corollary312 := 
  D.comparison.stage1Comparison_comparison_eq_corollary312

/-- Build a refinement from concrete signed data and a concrete target. -/
def stage1RefinementOf (thetaSigned qSigned targetSigned : Real)
    (hq : 0 < -qSigned) (hqt : qSigned ≤ targetSigned)
    (htt : targetSigned ≤ thetaSigned) : Stage1Refinement where
  comparison := { thetaSigned := thetaSigned, qSigned := qSigned,
    q_positive := hq, qSigned_le_thetaSigned := le_trans hqt htt }
  targetSigned := targetSigned
  q_le_target := hqt
  target_le_theta := htt

end LeanFormal.IUT.Objects.GogopexStage1
