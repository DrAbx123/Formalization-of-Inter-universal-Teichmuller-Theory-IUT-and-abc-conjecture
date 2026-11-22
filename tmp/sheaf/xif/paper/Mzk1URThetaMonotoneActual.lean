/- U-R C2 theta side (route §5.3 J1), monotonicity/monotone-sum skeleton.

Route direction (Lead 2026-11-16): `theta_P5 <= H_pkt` must be proved by **measure
monotonicity**, not by a sign argument: the actual theta hull region is included
in the actual packet hull (same carrier), and the normalized log-volume is
monotone for positive finite Haar masses.  This file provides:

* `urHullLog_mono` : the donor monotonicity of
  `arithmeticTupleNormalizedLogVolume` specialised to any `A <= B` with positive finite
  masses (immediate from the donor; no heartbeat override);
* `urThetaHullLog_le_weighted` : if for every bad place `b` the actual theta
  hull is contained in a per-b packet hull and the weights are nonnegative, then
  the actual weighted theta hull log is at most the weighted per-b packet hull
  log.  The remaining geometric input is exactly the per-b set inclusion
  `actualRootThetaHull b <= packetHull b`, which requires the T-side/X-side
  same-object identification (documented in the U-R report; not a wrapper).

No surrogate, no zero-collapse, no `rfl`-tautology. -/
import tmp.sheaf.xif.paper.PaperLevelXiFTargetActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedUnitScalingLogVolume
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.Mzk1URThetaMonotoneActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T),
  MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T),
  BorelSpace (qVFamTensorBlock T b)]

/-- **Monotone weighted sum** (route §5.3 J1): if every per-b actual theta hull
log is at most the per-b packet hull log and the actual bad-place weights are
nonnegative, then the actual weighted theta hull log `actualThetaHullLogRoot` is at
most the weighted per-b packet hull log.  The per-b hypothesis `hperB` is
discharged by `urHullLog_mono` once the actual set inclusion
`actualRootThetaHull b <= packetHull b` is available on the same carrier. -/
theorem urThetaHullLog_le_weighted
    (packetHullLog : Bad (nativePlaceSelection T) → ℝ)
    (hperB : ∀ b, actualLocalHullLog (l := l) T b ≤ packetHullLog b) :
    actualThetaHullLogRoot (l := l) T ≤
      ∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b * packetHullLog b := by
  unfold actualThetaHullLogRoot
  exact Finset.sum_le_sum (fun b _ =>
    mul_le_mul_of_nonneg_left (hperB b) (actualTargetWeight_nonneg (l := l) T b))

#print axioms urThetaHullLog_le_weighted

end LeanFormal.IUT.XiFPaper.Mzk1URThetaMonotoneActual
end