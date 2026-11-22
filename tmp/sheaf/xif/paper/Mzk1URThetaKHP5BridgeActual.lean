/- U-R C2 hP5 terminal reduction (kurt): from the paper q-degree comparison (an
explicit obligation) to -M_paper_v2 <= ksThetaHullLogRoot_lam.

This file does NOT prove the paper cross-slot comparison; it packages the reduction so
consumers (URC2Data.hP5) have a precise obligation shape.  DIRECTION (corrected 2026-11-17):
the sufficient comparison is S <= M_paper_v2 (S = sum_b thetaLamWeight_b*urCeilC_b*log p_b),
because -M <= -S chases with the hull lower bound -S <= ksThetaHullLogRoot_lam. The j1 file
Mzk1URThetaKHP5J1SameQActual gives hbridge_of_fiberLe for this direction.
  hbridge : sum_b thetaLamWeight_b * urCeilC_b * log p_b <= M_paper_v2
  => -M_paper_v2 <= ksThetaHullLogRoot_lam (via -M <= -S <= theta).

THIS FILE ONLY uses maxHeartbeats 1000000 (paper-level budget); RC registry: kurt-adapters-20261117 (1M heartbeats; Lead-approved list).
-/
import tmp.sheaf.xif.paper.Mzk1URThetaKHP5LamActual
import tmp.sheaf.xif.paper.Mzk1URThetaKLambdaAdapterActual
import tmp.sheaf.xif.paper.Mzk1ULQPilotMagnitudeV2Actual
import Mathlib.Tactic

noncomputable section
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.Mzk1URThetaKHP5BridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1ULKSideLettersActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKSideActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKHP5LamActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (ksBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (ksBlock T b)]

/-- terminal hP5 reduction: paper q-degree comparison implies -M_paper_v2 <= theta_lam. -/
theorem neg_MpaperV2_le_thetaLam_of_bridge
    (hbridge : (∑ b : Bad (nativePlaceSelection T),
        LeanFormal.IUT.XiFPaper.Mzk1URThetaKSideActual.thetaLamWeight T b * ((LeanFormal.IUT.XiFPaper.Mzk1URThetaKLowerCoreActual.urCeilC (l := l) T b) * Real.log
          ((completionRationalPrime (nativeBadToKPlace T b)).val : ℝ))) ≤
      LeanFormal.IUT.XiFPaper.Mzk1ULQPilotMagnitudeV2Actual.M_paper_v2 (l := l) T) :
    -LeanFormal.IUT.XiFPaper.Mzk1ULQPilotMagnitudeV2Actual.M_paper_v2 (l := l) T ≤
      LeanFormal.IUT.XiFPaper.Mzk1URThetaKSideActual.ksThetaHullLogRoot_lam (l := l) T := by
  have h : -(LeanFormal.IUT.XiFPaper.Mzk1ULQPilotMagnitudeV2Actual.M_paper_v2 (l := l) T) ≤
      -(∑ b : Bad (nativePlaceSelection T),
        LeanFormal.IUT.XiFPaper.Mzk1URThetaKSideActual.thetaLamWeight T b * ((LeanFormal.IUT.XiFPaper.Mzk1URThetaKLowerCoreActual.urCeilC (l := l) T b) * Real.log
          ((completionRationalPrime (nativeBadToKPlace T b)).val : ℝ))) :=
    neg_le_neg hbridge
  exact h.trans (ksThetaHullLogRoot_lam_lower (l := l) T)

#print axioms neg_MpaperV2_le_thetaLam_of_bridge

end LeanFormal.IUT.XiFPaper.Mzk1URThetaKHP5BridgeActual
end