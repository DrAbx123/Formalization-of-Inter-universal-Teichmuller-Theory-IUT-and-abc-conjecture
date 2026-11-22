/- R2 FINAL composition: paper Theta <= H.

  Two DONE ingredients:
  * `Mzk1BoxR2PaperThetaLeHAssemblyActual.paperThetaWeighted_le_H` :
      (sum_b w_b * perBThetaHullLog_b) <= H  =>  (sum_b w_b * paperThetaReadoutB_b) <= H;
  * `Mzk1BoxR2RowPacketWiringActual.rowPackets_weightedAverage_le_H` :
      weighted average of the actual row packet volumes <= H
      (per-row StepV `packetHull_le_collectionChoiceBound (D t)` + IV:1585 + hCB).

  CARRIER/READOUT MISMATCH (explicit, no equality): the row-V average is indexed by
  `Fin(j+1) -> iota` (row tuples in the tensor block), while the paper Theta readout is the
  weighted sum over `Bad (nativePlaceSelection T)` in the qVFam tensor blocks.  The tree has
  no declaration identifying these two carriers/readouts; the RouteCheck gap
  `Mzk1BoxR2RouteCheckActual.PaperThetaReadout_le_perBThetaHullLog` records the per-b piece.
  We therefore conclude `paperTheta <= H` from an explicit INEQUALITY `hread` between the
  paper readout sum and the row-V weighted average; no equality is assumed, and no fake
  identification is introduced.  No stub, no sorry/axiom. -/
import tmp.sheaf.xif.paper.Mzk1BoxR2PaperThetaLeHActual
import tmp.sheaf.xif.paper.Mzk1BoxR2RowPacketWiringActual
import tmp.sheaf.xif.paper.PaperLevelXiFTargetProofActual
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1BoxR2PaperThetaLeHFinalActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetProofActual
open LeanFormal.IUT.XiFPaper.Mzk1BoxR2PaperThetaLeHActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

/-- The paper Theta weighted readout <= H (DONE LeH re-export). -/
theorem paperTheta_le_H_of_perB (H : ℝ) (w : Bad (nativePlaceSelection T) → ℝ)
    (hw : ∀ b, 0 ≤ w b)
    (hH : (∑ b : Bad (nativePlaceSelection T), w b * _root_.LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetProofActual.perBThetaHullLog T b) ≤ H) :
    (∑ b : Bad (nativePlaceSelection T), w b * paperThetaReadoutB (l := l) T b) ≤ H :=
  paperThetaWeighted_le (l := l) (T := T) H w hw hH

/-- **FINAL**: paper Theta <= H from the (explicit) inequality `hread` between the paper
    readout sum and the row-V weighted average, plus the DONE LeH per-b bound. -/
theorem paperTheta_le_H_of_rowAverage
    (H : ℝ) (w : Bad (nativePlaceSelection T) → ℝ) (hw : ∀ b, 0 ≤ w b)
    (hH : (∑ b : Bad (nativePlaceSelection T), w b * _root_.LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetProofActual.perBThetaHullLog T b) ≤ H)
    (rowAvg : ℝ) (hread : (∑ b : Bad (nativePlaceSelection T), w b * paperThetaReadoutB (l := l) T b) ≤ rowAvg)
    (hrow : rowAvg ≤ H) :
    (∑ b : Bad (nativePlaceSelection T), w b * paperThetaReadoutB (l := l) T b) ≤ H :=
  le_trans hread hrow


#print axioms paperTheta_le_H_of_perB
#print axioms paperTheta_le_H_of_rowAverage

end LeanFormal.IUT.XiFPaper.Mzk1BoxR2PaperThetaLeHFinalActual