import tmp.sheaf.xif.paper.S2594HpointWiringActual
import tmp.sheaf.xif.paper.S2590PadicSingletonNullActual
import tmp.sheaf.xif.paper.S2720BridgeHaarActual
import tmp.sheaf.xif.paper.S2722HunitDActual
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 800000

namespace LeanFormal.IUT.XiFPaper.S2721BridgeSkeletonActual

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S2586IQHullLogVolumeInstantiationActual
open LeanFormal.IUT.XiFPaper.S2588RationalPointMapActual
open LeanFormal.IUT.XiFPaper.S2589DictionaryMinimalActual
open LeanFormal.IUT.XiFPaper.S2590PadicSingletonNullActual
open LeanFormal.IUT.XiFPaper.S2594HpointWiringActual
open LeanFormal.IUT.XiFPaper.S2720BridgeHaarActual
open LeanFormal.IUT.XiFPaper.S2722HunitDActual

universe u

/-- Generic two-gap bridge data: all hull/log-volume/point objects are real, and
the two paper comparison links are explicit fields. -/
structure S2721BridgeData (X : Type u) where
  hullData : IQHullLogVolumeInterface X
  logShellPoint : Nat → Nat → Nat → X
  height_le_normalizedRegionVolume :
    ∀ (epsilon : Real), 0 < epsilon → ∀ a n c : Nat, IsABCTriple a n c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + epsilon) *
          (hullData.logVolume
            (normalizedComparisonRegion hullData logShellPoint a n c)).toReal
  regionVolume_le_normalizedWeight :
    ∀ (epsilon : Real), 0 < epsilon → ∃ D : Real,
      ∀ a n c : Nat, IsABCTriple a n c →
        (hullData.logVolume
          (normalizedComparisonRegion hullData logShellPoint a n c)).toReal ≤
          (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) +
            (hullData.logVolume hullData.hull).toReal + D

/-- Conditional bridge from the generic two-gap data. -/
noncomputable def S2721_bridge_of_data {X : Type u} (D : S2721BridgeData X) :
    Cor312ToABCBridgeInterface where
  carrier := X
  hullData := D.hullData
  epsilonComparison := fun epsilon heps =>
    { logShellPoint := D.logShellPoint
      height_le_normalizedRegionVolume :=
        D.height_le_normalizedRegionVolume epsilon heps
      regionVolume_le_normalizedWeight :=
        D.regionVolume_le_normalizedWeight epsilon heps }

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable [MeasurableSpace (qVFamTensorBlock T b)]
variable [BorelSpace (qVFamTensorBlock T b)]

/-- Real-object per-epsilon comparison: logShellPoint is S2588PointMap, the
region field uses the actual S2722 hunitD/D0/gap2 assembly (no hardcoded D0 = 0),
and the height gap is explicit. -/
noncomputable def S2721_epsilonComparisonS2586
    (eps : Real) (heps : 0 < eps)
    (hheight : ∀ a n c : Nat, IsABCTriple a n c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + eps) *
          ((S2586IQHullLogVolumeInterface (l := l) T b).logVolume
            (normalizedComparisonRegion (S2586IQHullLogVolumeInterface (l := l) T b)
              (S2588PointMap (l := l) T b) a n c)).toReal)
    (hval : ∀ a n c : Nat, IsABCTriple a n c →
      ∀ q : Nat, q ∈ arithmeticPrimeSupport (abcRationalPoint a c) →
        max 0 (-(padicValRat q (abcRationalPoint a c) : Real)) ≤ 1 + eps) :
    Cor312EpsilonArithmeticComparison
      (S2586IQHullLogVolumeInterface (l := l) T b) eps where
  logShellPoint := S2588PointMap (l := l) T b
  height_le_normalizedRegionVolume := hheight
  regionVolume_le_normalizedWeight :=
    S2722_gap2_with_D0 (l := l) T b eps
      (S2594_pointBound (l := l) T b (S2590SingletonNull (l := l) T b)
        (le_of_lt heps) hval)

/-- Real-object conditional bridge over the S2586 carrier, S2588 point map and
S2722 D0/hunitD/gap2 assembly.  hval and hweightvol are kept explicit; hweightvol
is the paper weight/region comparison gap (not consumed by the D0-based gap-2
route, but retained as an explicit interface input).  The bridge is not closed:
hheight (gap 1) and hval/hweightvol remain inputs. -/
noncomputable def S2721_bridgeS2586
    (hheight : ∀ (eps : Real), 0 < eps →
      ∀ a n c : Nat, IsABCTriple a n c →
        Height.logHeight₁ (abcRationalPoint a c) ≤
          (1 + eps) *
            ((S2586IQHullLogVolumeInterface (l := l) T b).logVolume
              (normalizedComparisonRegion (S2586IQHullLogVolumeInterface (l := l) T b)
                (S2588PointMap (l := l) T b) a n c)).toReal)
    (hval : ∀ (eps : Real), 0 < eps →
      ∀ a n c : Nat, IsABCTriple a n c →
        ∀ q : Nat, q ∈ arithmeticPrimeSupport (abcRationalPoint a c) →
          max 0 (-(padicValRat q (abcRationalPoint a c) : Real)) ≤ 1 + eps)
    (_hweightvol : ∀ a n c : Nat, IsABCTriple a n c →
      arithmeticWeight (abcRationalPoint a c) ≤
        ((S2586IQHullLogVolumeInterface (l := l) T b).logVolume
          (normalizedComparisonRegion (S2586IQHullLogVolumeInterface (l := l) T b)
            (S2588PointMap (l := l) T b) a n c)).toReal) :
    Cor312ToABCBridgeInterface where
  carrier := qVFamTensorBlock T b
  hullData := S2586IQHullLogVolumeInterface (l := l) T b
  epsilonComparison := fun eps heps =>
    S2721_epsilonComparisonS2586 (l := l) T b eps heps
      (hheight eps heps) (hval eps heps)

/-- The real carrier of the conditional bridge. -/
theorem S2721_bridgeS2586_carrier (hheight hval hweightvol) :
    (S2721_bridgeS2586 (l := l) T b hheight hval hweightvol).carrier
      = qVFamTensorBlock T b := rfl

end LeanFormal.IUT.XiFPaper.S2721BridgeSkeletonActual
end
