/- PIECE 5 (R2): assemble `hread : sum_b w_b * paperThetaReadoutB_b <= rowAvg` and the
  final `paperTheta <= H`.

  The actual per-b paper Theta readout `paperThetaReadoutB_b` is the `rootNormHull`
  normalized log-volume, and the DONE `Mzk1BoxR2RouteCheckActual` per-b comparison
  (`paperThetaReadout_le_perBThetaHullLog_instance`) gives it `<= perBThetaHullLog_b`.
  Therefore, for nonnegative weights, the weighted sum is `<= sum_b w_b * perBThetaHullLog_b`;
  taking `rowAvg := sum_b w_b * perBThetaHullLog_b` this is exactly `hread`.
  The final step `rowAvg <= H -> sum_b w_b * paperThetaReadoutB_b <= H` is the DONE
  `Mzk1BoxR2PaperThetaLeHFinalActual.paperTheta_le_H_of_rowAverage`.
  No equality, no stub, no sorry/axiom. -/
import tmp.sheaf.xif.paper.Mzk1BoxR2PaperThetaLeHFinalActual
import tmp.sheaf.xif.paper.Mzk1BoxR2RouteCheckActual
import tmp.sheaf.xif.paper.PaperLevelXiFTargetProofActual
import Mathlib.Tactic

noncomputable section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1G1F2R2HreadActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1BoxR2PaperThetaLeHActual
open LeanFormal.IUT.XiFPaper.Mzk1BoxR2PaperThetaLeHFinalActual
open LeanFormal.IUT.XiFPaper.Mzk1BoxR2RouteCheckActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetProofActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

/-- **PIECE 5 hread**: weighted paper Theta readout <= weighted per-b hull logs. -/
theorem hread_actual (w : Bad (nativePlaceSelection T) → ℝ) (hw : ∀ b, 0 ≤ w b) :
    (∑ b : Bad (nativePlaceSelection T), w b * paperThetaReadoutB (l := l) T b) ≤
      ∑ b : Bad (nativePlaceSelection T),
        w b * PaperLevelXiFTargetProofActual.perBThetaHullLog T b := by
  apply Finset.sum_le_sum
  intro b _
  exact mul_le_mul_of_nonneg_left
    (paperThetaReadout_le_perBThetaHullLog_instance (l := l) T b) (hw b)

/-- **PIECE 5 final**: paper Theta <= H from the weighted per-b hull-log bound. -/
theorem paperTheta_le_H_final (H : ℝ) (w : Bad (nativePlaceSelection T) → ℝ)
    (hw : ∀ b, 0 ≤ w b)
    (hH : (∑ b : Bad (nativePlaceSelection T),
        w b * PaperLevelXiFTargetProofActual.perBThetaHullLog T b) ≤ H) :
    (∑ b : Bad (nativePlaceSelection T), w b * paperThetaReadoutB (l := l) T b) ≤ H :=
  paperTheta_le_H_of_rowAverage (l := l) T H w hw hH
    (∑ b : Bad (nativePlaceSelection T),
      w b * PaperLevelXiFTargetProofActual.perBThetaHullLog T b)
    (hread_actual (l := l) T w hw) hH

#print axioms hread_actual
#print axioms paperTheta_le_H_final

/-- **R2 upper reduction**: the real missing R2 upper is `sum w * perBThetaHullLog <= rowAvgP`
    (row-packet weighted average) followed by `rowAvgP <= H`.  This lemma records the exact
    reduction; it does NOT close R2. -/
theorem r2_upper_via_rowAvg
    (H : ℝ) (w : Bad (nativePlaceSelection T) → ℝ) (hw : ∀ b, 0 ≤ w b)
    (rowAvgP : ℝ)
    (hbridge : (∑ b : Bad (nativePlaceSelection T),
        w b * PaperLevelXiFTargetProofActual.perBThetaHullLog T b) ≤ rowAvgP)
    (hrow : rowAvgP ≤ H) :
    (∑ b : Bad (nativePlaceSelection T),
      w b * PaperLevelXiFTargetProofActual.perBThetaHullLog T b) ≤ H :=
  le_trans hbridge hrow

#print axioms r2_upper_via_rowAvg

end LeanFormal.IUT.XiFPaper.Mzk1G1F2R2HreadActual