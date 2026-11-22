/- K-side theta/H_pkt scale declaration (kurt) for sophie's C2ThetaInputK.

Scale statement (paper ruling):
* ksThetaHullLogRoot_lam = Sum_b thetaLamWeight_b * ksThetaHullLog_b, where ksThetaHullLog_b is the
  normalized log volume of the nonzero-label theta hull built from urCeilC = ceil(c1*e)/e, i.e. the
  ROOT / M-scale coefficient (c_norm/e = local q order / (2l)); so theta_lambda is an M-scale readout.
* ucWeightedHpkt w V = Sum_i w_i * V_i is a generic weighted sum; when V_i is a hull log volume
  (as in the C2 theta side / StepV packet bound) it is at the same M scale.
Consequently ksThetaHullLogRoot_lam and the C2 theta side live in the SAME M scale; the only
Q-scale object in the old tree is actualQPilotMagnitudeClassical, which must not be used as the C2 Q.

Default heartbeats.
-/
import tmp.sheaf.xif.paper.Mzk1URThetaKSideActual
import tmp.sheaf.xif.paper.Mzk1UCC3ProducerActual
import Mathlib.Tactic

noncomputable section
open scoped BigOperators Pointwise

namespace LeanFormal.IUT.XiFPaper.Mzk1URThetaKScaleActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1ULKSideLettersActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKSideActual
open LeanFormal.IUT.XiFPaper.Mzk1UCC3ProducerActual
open MeasureTheory

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (ksBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (ksBlock T b)]

/-- Lambda-weighted theta root is the weighted sum of per-b hull log volumes. -/
theorem ksThetaHullLogRoot_lam_scale :
    ksThetaHullLogRoot_lam (l := l) T =
      ∑ b : Bad (nativePlaceSelection T),
        thetaLamWeight T b * ksThetaHullLog (l := l) T b := rfl

/-- Per-b theta hull log is the normalized log volume of the nonzero-label hull. -/
theorem ksThetaHullLog_scale (b : Bad (nativePlaceSelection T)) :
    ksThetaHullLog (l := l) T b =
      arithmeticTupleNormalizedLogVolume (ksPlaces T b) ksTuple
        MeasureTheory.Measure.addHaar (ksThetaHull (l := l) T b) := rfl

/-- The generic weighted packet hull is the weighted sum of the given hull volumes. -/
theorem ucWeightedHpkt_scale {ι : Type} [Fintype ι] (w V : ι → ℝ) :
    ucWeightedHpkt w V = ∑ i, w i * V i := rfl

/-- Weighted paper upper bound in the same scale. -/
theorem ucWeightedHpkt_scale_le {ι : Type} [Fintype ι] (w V paper : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hp : ∀ i, V i ≤ paper i) :
    ucWeightedHpkt w V ≤ ∑ i, w i * paper i := by
  rw [ucWeightedHpkt_scale]
  exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hp i) (hw i))

#print axioms ksThetaHullLogRoot_lam_scale
#print axioms ksThetaHullLog_scale
#print axioms ucWeightedHpkt_scale

end LeanFormal.IUT.XiFPaper.Mzk1URThetaKScaleActual
end