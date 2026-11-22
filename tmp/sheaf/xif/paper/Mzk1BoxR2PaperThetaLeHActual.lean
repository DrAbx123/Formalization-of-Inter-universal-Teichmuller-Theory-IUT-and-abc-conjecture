/- R2 composition (kurt): paper Theta weighted readout <= H, from the DONE readout identification
(Mzk1BoxR2RouteCheckActual.paperThetaReadout_le_perBThetaHullLog_instance, trio 22:35:22) and the
weighted StepV bound on perBThetaHullLog.  Only inequalities are used.

Missing bridge documented here (not stubbed): the StepV/box bound of RowV is stated for the PACKET-hull
volume `arithmeticTupleNormalizedLogVolume ... (packetHull D)`, while the readout chain ends at
`perBThetaHullLog`.  S716 gives readout(rootNormHull) = perBThetaHullLog; no DONE lemma identifies
perBThetaHullLog with packetHull volume, so the final identification is left as the explicit
hypothesis hH below.
-/
import tmp.sheaf.xif.paper.Mzk1BoxR2RouteCheckActual
import tmp.sheaf.xif.paper.RootNormalizedContainmentActual
import tmp.sheaf.xif.paper.RootHullContainmentInequalityActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedUnitScalingLogVolume
import Mathlib.Tactic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 4000000

noncomputable section
open scoped BigOperators
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.RootNormalizedContainmentActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.Mzk1BoxR2PaperThetaLeHActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open MeasureTheory
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1BoxR2RouteCheckActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetProofActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

/-- The actual per-b paper Theta readout: normalized log-volume of `rootNormHull`
    (the route paper Θ object, spectral `c_P/(2l)`).  Named locally to keep the later
    theorem statement small. -/
noncomputable def paperThetaReadoutB (b : Bad (nativePlaceSelection T)) : ℝ :=
  arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple
    Measure.addHaar (rootNormHull (l := l) T b)

/-- Weighted paper-Theta readout is bounded by H, given the weighted per-b bound on
`perBThetaHullLog` (the only missing identification is the packet-hull vs readout bridge). -/
theorem paperThetaWeighted_le (H : ℝ) (w : Bad (nativePlaceSelection T) → ℝ)
    (hw : ∀ b, 0 ≤ w b)
    (hH : (∑ b : Bad (nativePlaceSelection T), w b * perBThetaHullLog T b) ≤ H) :
    (∑ b : Bad (nativePlaceSelection T), w b * paperThetaReadoutB (l := l) T b) ≤ H := by
  refine le_trans ?_ hH
  apply Finset.sum_le_sum
  intro b _
  exact mul_le_mul_of_nonneg_left
    (paperThetaReadout_le_perBThetaHullLog_instance (l := l) T b) (hw b)




end LeanFormal.IUT.XiFPaper.Mzk1BoxR2PaperThetaLeHActual
end