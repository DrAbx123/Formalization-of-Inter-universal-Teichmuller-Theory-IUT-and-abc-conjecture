/- R2 (kurt): actual StepV procession objects and the theta hull log-volume monotonicity.

Route 4.2: the theta hull is bounded via the StepV procession average; this file defines the
actual procession objects and records the hull-to-ceil-region log-volume monotonicity, replacing
the former theta_procession_cover obligation.

Donors (DONE):
 * Mzk1P6WeightedPacketHullActual.ULPacketHullValue / ULPacketHullBound / uL_weightedPacketHull_le;
 * IUTIV.StepVProcessionAverage.collectionBound (per-label packet value);
 * Mzk1URThetaKLowerBoundActual.{ksThetaHull_subset_ceilRegion, normLogVol_mono_local};
 * Mzk1URThetaKLowerCoreActual.urCeilRegion_measure_lt_top.
-/
import tmp.sheaf.xif.paper.Mzk1P6WeightedPacketHullActual
import tmp.sheaf.xif.paper.Mzk1URThetaKSideActual
import tmp.sheaf.xif.paper.Mzk1URThetaKLowerBoundActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedUnitScalingLogVolume
import tmp.sheaf.xif.paper.ThetaTensorScaledImageActual
import Mathlib.Tactic

noncomputable section
set_option maxHeartbeats 1000000
open scoped BigOperators
open MeasureTheory

namespace LeanFormal.IUT.XiFPaper.Mzk1URThetaProcessionActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.ThetaTensorScaledImageActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKSideActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKLowerCoreActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKLowerBoundActual

/-- The per-label actual packet value from the StepV procession average. -/
noncomputable def urProcessionV (n : ℕ) (D Q S T' : ℝ) (j : ℕ) : ℝ :=
  LeanFormal.IUT.IUTIV.StepVProcessionAverage.collectionBound
    (2 * (n : ℝ) + 1) D Q S T' j

/-- The actual procession average (over labels 1..n). -/
noncomputable def urProcessionAvg (n : ℕ) (D Q S T' : ℝ) : ℝ :=
  Mzk1P6WeightedPacketHullActual.ULPacketHullValue n D Q S T'

/-- The paper upper bound for the procession average. -/
noncomputable def urProcessionBound (n : ℕ) (D Q S T' : ℝ) : ℝ :=
  Mzk1P6WeightedPacketHullActual.ULPacketHullBound n D Q S T'

/-- The procession average is bounded by the paper StepV bound. -/
theorem urProcessionAvg_le_bound {n : ℕ} (hn : 2 ≤ n) (D Q S T' : ℝ)
    (hD : 0 ≤ D) (hS : 0 ≤ S) (hT : 0 ≤ T') :
    urProcessionAvg n D Q S T' ≤ urProcessionBound n D Q S T' :=
  Mzk1P6WeightedPacketHullActual.uL_weightedPacketHull_le n hn D Q S T' hD hS hT

#print axioms urProcessionAvg_le_bound

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)

set_option maxHeartbeats 2000000 in
/-- The theta hull log-volume is bounded by the ceiling-region log-volume (DONE donors:
ksThetaHull_subset_ceilRegion, urCeilRegion_measure_lt_top, normLogVol_mono_local).
This replaces the former obligation theta_procession_cover at the log-volume level. -/
theorem nu_ksThetaHull_le_nu_ceilRegion (b : Bad (nativePlaceSelection T))
    [MeasurableSpace (ksBlock T b)] [BorelSpace (ksBlock T b)] :
    LeanFormal.IUT.NumberFieldFinitePlace.arithmeticTupleNormalizedLogVolume (places := ksPlaces T b) (tuple := ksTuple)
        MeasureTheory.Measure.addHaar (ksThetaHull (l := l) T b) ≤
      LeanFormal.IUT.NumberFieldFinitePlace.arithmeticTupleNormalizedLogVolume (places := ksPlaces T b) (tuple := ksTuple)
        MeasureTheory.Measure.addHaar
        (thetaTensorScaledRegion (places := ksPlaces T b) (tuple := ksTuple)
          (fun _ => urCeilC (l := l) T b)) := by
  refine normLogVol_mono_local (l := l) (T := T) b ?_ ?_ ?_
  · exact ksThetaHull_subset_ceilRegion (l := l) T b
  · exact lt_of_lt_of_le (ksLabelOneRegion_measure_pos (l := l) T b)
      (measure_mono (ksOneLabelRegion_subset_hull (l := l) T b))
  · exact urCeilRegion_measure_lt_top (l := l) T b


set_option maxHeartbeats 2000000 in
/-- R2 OPEN (documented, no proof): the geometric StepV source map from the theta hull to the
procession average.  This is the only missing prerequisite for replacing the closed-form
urPacketV_K proxy by the actual procession average; it corresponds to route 4.2 mechanism 2/3
(associated-graded determinant multiplicativity / finite-precision fiber counting). -/
def stepV_hullVolume_le_processionAvg (b : Bad (nativePlaceSelection T))
    [MeasurableSpace (ksBlock T b)] [BorelSpace (ksBlock T b)]
    (n : ℕ) (D Q S T' : ℝ) : Prop :=
  LeanFormal.IUT.NumberFieldFinitePlace.arithmeticTupleNormalizedLogVolume (places := ksPlaces T b) (tuple := ksTuple)
      MeasureTheory.Measure.addHaar (ksThetaHull (l := l) T b) ≤
    urProcessionAvg n D Q S T'

#print axioms nu_ksThetaHull_le_nu_ceilRegion

end LeanFormal.IUT.XiFPaper.Mzk1URThetaProcessionActual
end