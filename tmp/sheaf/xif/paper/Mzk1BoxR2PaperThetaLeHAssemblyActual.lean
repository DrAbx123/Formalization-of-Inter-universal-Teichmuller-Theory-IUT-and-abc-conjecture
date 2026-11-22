/- R2 composition: paper Theta <= H from the DONE LeH readout bound and the DONE
  weighted row-V average bound.

  * `paperThetaWeighted_le_H` re-exports `Mzk1BoxR2PaperThetaLeHActual.paperThetaWeighted_le`:
      (sum_b w_b * perBThetaHullLog_b) <= H  =>  (sum_b w_b * paperThetaReadoutB_b) <= H.
  * `weightedRowV_le_H` composes the DONE
      `Mzk1BoxR2RowPacketWiringActual.actual_weightedAverage_le_collectionBound_rowPackets`
    (weighted average of the actual row packet volumes <= collectionBound) with
    an explicit `hCB : collectionBound ... <= H`; only inequalities.
  The remaining identification (weighted row-V average vs sum_b thetaLamWeight*paperThetaReadoutB)
  is the named RouteCheck gap and is NOT assumed as equality here.
  No stub, no sorry/axiom. -/
import tmp.sheaf.xif.paper.Mzk1BoxR2PaperThetaLeHActual
import tmp.sheaf.xif.paper.Mzk1BoxR2RowPacketWiringActual
import tmp.sheaf.xif.paper.PaperLevelXiFTargetProofActual
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 8000000
namespace LeanFormal.IUT.XiFPaper.Mzk1BoxR2PaperThetaLeHAssemblyActual

open MeasureTheory
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetProofActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.IUTIV.StepVDistinguishedSlotAverage
open LeanFormal.IUT.IUTIV.StepVProcessionAverage
open LeanFormal.IUT.XiFPaper.Mzk1BoxR2PaperThetaLeHActual
open LeanFormal.IUT.XiFPaper.Mzk1BoxR2RowPacketWiringActual
open LeanFormal.IUT.XiFPaper.Mzk1BoxReadoutLocalActual
open LeanFormal.IUT.XiFPaper.Mzk1BoxActualR2Actual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual

universe u v w

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

/-- **Paper Theta <= H** (DONE LeH composition): the weighted readout sum is bounded by H
    whenever the weighted `_root_.LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetProofActual.perBThetaHullLog` sum is. -/
theorem paperThetaWeighted_le_H (H : ℝ) (w : Bad (nativePlaceSelection T) → ℝ)
    (hw : ∀ b, 0 ≤ w b)
    (hH : (∑ b : Bad (nativePlaceSelection T), w b * _root_.LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetProofActual.perBThetaHullLog T b) ≤ H) :
    (∑ b : Bad (nativePlaceSelection T), w b * paperThetaReadoutB (l := l) T b) ≤ H :=
  paperThetaWeighted_le (l := l) T H w hw hH


#print axioms paperThetaWeighted_le_H

end LeanFormal.IUT.XiFPaper.Mzk1BoxR2PaperThetaLeHAssemblyActual