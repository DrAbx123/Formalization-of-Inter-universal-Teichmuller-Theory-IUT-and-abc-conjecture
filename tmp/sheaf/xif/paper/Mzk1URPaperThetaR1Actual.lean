/- R1 paper Theta assembly (kurt): sole remaining scalar input hW.

hW : nativeBadLocalWeight_b * cNorm_b = (1/(2l)) * cPFullFiber_b.
Under hW, M_paper_v2 equals the paper weighted q-pilot magnitude, and the DONE paper Theta
inequality (PaperLevelXiFTargetBridgeActual.actualPaperXiFTarget) gives
  -M_paper_v2 <= actualThetaHullLogRoot,   actualThetaHullLogRoot = Sum_b weight_b * perBThetaHullLog_b,
with perBThetaHullLog the ACTUAL root Theta hull = paper Theta (rootThetaHull of gauss*cRoot rows).
-/
import tmp.sheaf.xif.paper.PaperLevelXiFTargetBridgeActual
import tmp.sheaf.xif.paper.Mzk1ULOrdFiberTowerActual
import tmp.sheaf.xif.paper.Mzk1ULQPilotMagnitudeV2Actual
import tmp.sheaf.xif.paper.Mzk1ULR1MpaperBWeightActual
import tmp.sheaf.xif.paper.Mzk1ULR1CPrimeFiberActual
import tmp.sheaf.xif.paper.Mzk1URRootNuOnePlaceActual
import tmp.sheaf.xif.paper.QVFamNormalizedGeneratorSupplyActual
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace LeanFormal.IUT.XiFPaper.Mzk1URPaperThetaR1Actual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetBridgeActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Main assembly: under hW, -(M_paper_v2) <= the paper Theta hull log. -/
theorem negMpaperV2_le_actualThetaHullLogRoot
    (hW : ∀ b : Bad (nativePlaceSelection T),
      LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual.nativeBadLocalWeight T b *
          LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b =
        (1 / (2 * (l.value : ℝ))) *
          LeanFormal.IUT.XiFPaper.Mzk1ULR1CPrimeFiberActual.cPFullFiber T b) :
    -LeanFormal.IUT.XiFPaper.Mzk1ULQPilotMagnitudeV2Actual.M_paper_v2 T ≤
      LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetActual.actualThetaHullLogRoot T := by
  have hM : LeanFormal.IUT.XiFPaper.Mzk1ULQPilotMagnitudeV2Actual.M_paper_v2 T =
      LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetActual.actualQPilotMagnitudeClassical T := by
    rw [LeanFormal.IUT.XiFPaper.Mzk1ULOrdFiberTowerActual.M_paper_v2_eq_sum_MpaperB T]
    unfold LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetActual.actualQPilotMagnitudeClassical
    apply Finset.sum_congr rfl
    intro b _
    have hq := LeanFormal.IUT.XiFPaper.Mzk1ULR1MpaperBWeightActual.MpaperB_eq_neg_qPilotMass T b
    rw [hq, LeanFormal.IUT.XiFPaper.Mzk1URRootNuOnePlaceActual.qPilotMass_eq]
    rw [hW b]
    ring
  rw [hM]
  have h := LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetBridgeActual.actualPaperXiFTarget T
  unfold LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetActual.ActualPaperXiFTarget at h
  unfold LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetActual.actualQPilotSignedLogClassical at h
  linarith

#print axioms negMpaperV2_le_actualThetaHullLogRoot

end LeanFormal.IUT.XiFPaper.Mzk1URPaperThetaR1Actual
end