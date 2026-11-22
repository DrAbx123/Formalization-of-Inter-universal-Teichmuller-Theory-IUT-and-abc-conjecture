import tmp.sheaf.xif.paper.S2722HunitDActual
import tmp.sheaf.xif.paper.S2722HpointActual
import tmp.sheaf.xif.paper.S2720BridgeHaarActual

/-! # Stage-4 host: mining the old attempts — hunit/hsplit/hptfin already wired

PRIOR ART (§7.9, checked first):
* S2722HunitDActual.lean:34 S2722D0 (actual nonnegative constant), :44 S2722_hunitD
  (unit-region bound PROVED with the actual D0), :68 S2722_gap2_with_D0 (gap-2
  reduction with hunit discharged; hsplit supplied by S2720BridgeHaarActual:70
  normalizedRegion_logVolume_le_split; hptfin by singleton-null; only hpoint is a
  named input there);
* S2722HpointActual.lean:30 S2722_hpoint (hpoint via S2590SingletonNull).

WHAT THIS FILE DOES: exposes the old-attempt wiring pieces as reuse adapters for the
(c) obligations (unit-region bound = hunit; split-point bound = hsplit; point
finiteness = hptfin; point bound = hpoint).  HONESTY: hunit/hsplit/hptfin are genuine
measure facts on the S2586 carrier, but hpoint is degenerate (singleton log-volumes
are 0 because Haar singletons are null), so the point-bound slot is NOT the paper's
point-height comparison.

LABEL: reuse adapters (old-attempt prior art) + honesty flags. Registry frozen; new
file only. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3136OldSplitPointUnitRegionWiringActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S2586IQHullLogVolumeInstantiationActual
open LeanFormal.IUT.XiFPaper.S2588RationalPointMapActual
open LeanFormal.IUT.XiFPaper.S2722HunitDActual
open LeanFormal.IUT.XiFPaper.S2722HpointActual
open LeanFormal.IUT.XiFPaper.S2720BridgeHaarActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable [MeasurableSpace (qVFamTensorBlock T b)]
variable [BorelSpace (qVFamTensorBlock T b)]

/-- Reuse: the actual nonnegative D0 of the old attempt. -/
theorem lgpOldD0_nonneg : 0 ≤ S2722D0 (l := l) T b := S2722D0_nonneg (l := l) T b

/-- Reuse: the unit-region bound (hunit) with the actual D0, PROVED in the old attempt. -/
theorem lgpOldHunitD :
    (S2586IQHullLogVolumeInterface (l := l) T b).logVolume
        (S2586IQHullLogVolumeInterface (l := l) T b).unitRegion
      ≤ (S2586IQHullLogVolumeInterface (l := l) T b).logVolume
          (S2586IQHullLogVolumeInterface (l := l) T b).hull +
        ENNReal.ofReal (S2722D0 (l := l) T b) :=
  S2722_hunitD (l := l) T b

/-- Reuse: the per-triple split (hsplit) from the old attempt. -/
theorem lgpOldSplit (point : Nat → Nat → Nat → qVFamTensorBlock T b) (a n c : Nat) :
    (S2586IQHullLogVolumeInterface (l := l) T b).logVolume
        ((S2586IQHullLogVolumeInterface (l := l) T b).scaleShift ''
          ((S2586IQHullLogVolumeInterface (l := l) T b).unitRegion ∪ {point a n c}))
      ≤ (S2586IQHullLogVolumeInterface (l := l) T b).logVolume
          ((S2586IQHullLogVolumeInterface (l := l) T b).scaleShift ''
            (S2586IQHullLogVolumeInterface (l := l) T b).unitRegion)
        + (S2586IQHullLogVolumeInterface (l := l) T b).logVolume
            {(S2586IQHullLogVolumeInterface (l := l) T b).scaleShift (point a n c)} :=
  normalizedRegion_logVolume_le_split (l := l) T b point a n c

/-- Reuse: the old attempt's hpoint (DEGENERATE: singleton null). -/
theorem lgpOldHpointDegenerate {eps : ℝ} (heps : 0 ≤ eps) :
    ∀ a n c : Nat, IsABCTriple a n c →
      ((S2586IQHullLogVolumeInterface (l := l) T b).logVolume
        {(S2586IQHullLogVolumeInterface (l := l) T b).scaleShift
          (S2588PointMap (l := l) T b a n c)}).toReal
      ≤ (1 + eps) * arithmeticWeight (abcRationalPoint a c) :=
  S2722_hpoint (l := l) T b eps heps

/-- Reuse: the old attempt's gap-2 reduction with hunit discharged and hpoint named. -/
theorem lgpOldGap2WithD0 (eps : ℝ)
    (hpoint : ∀ a n c : Nat, IsABCTriple a n c →
      ((S2586IQHullLogVolumeInterface (l := l) T b).logVolume
        {(S2586IQHullLogVolumeInterface (l := l) T b).scaleShift
          (S2588PointMap (l := l) T b a n c)}).toReal
      ≤ (1 + eps) * arithmeticWeight (abcRationalPoint a c)) :
    ∃ D : ℝ, ∀ a n c : Nat, IsABCTriple a n c →
      ((S2586IQHullLogVolumeInterface (l := l) T b).logVolume
        (normalizedComparisonRegion
          (S2586IQHullLogVolumeInterface (l := l) T b)
          (S2588PointMap (l := l) T b) a n c)).toReal
      ≤ (1 + eps) * arithmeticWeight (abcRationalPoint a c) +
          ((S2586IQHullLogVolumeInterface (l := l) T b).logVolume
            (S2586IQHullLogVolumeInterface (l := l) T b).hull).toReal + D :=
  S2722_gap2_with_D0 (l := l) T b eps hpoint

#check lgpOldD0_nonneg
#check lgpOldHunitD
#check lgpOldSplit
#check lgpOldHpointDegenerate
#check lgpOldGap2WithD0

end LeanFormal.IUT.XiFPaper.S3136OldSplitPointUnitRegionWiringActual
end