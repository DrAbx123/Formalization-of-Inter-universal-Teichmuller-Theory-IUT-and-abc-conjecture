import tmp.sheaf.xif.paper.S2586IQHullLogVolumeInstantiationActual
import tmp.sheaf.xif.paper.S2588RationalPointMapActual
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2720BridgeSkeletonActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S2586IQHullLogVolumeInstantiationActual
open LeanFormal.IUT.XiFPaper.S2588RationalPointMapActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable [MeasurableSpace (qVFamTensorBlock T b)]
variable [BorelSpace (qVFamTensorBlock T b)]

/-- The two unproved paper links of the per-epsilon bridge, frozen as explicit
Prop fields over the actual qVFam tensor carrier. -/
structure BridgeGapData (epsilon : Real) (_heps : 0 < epsilon) where
  height_le_normalizedRegionVolume :
    ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + epsilon) *
          ((S2586IQHullLogVolumeInterface (l := l) T b).logVolume
            (normalizedComparisonRegion
              (S2586IQHullLogVolumeInterface (l := l) T b)
              (S2588PointMap (l := l) T b) a b c)).toReal
  regionVolume_le_normalizedWeight :
    ∃ D : Real, ∀ a b c : Nat, IsABCTriple a b c →
      ((S2586IQHullLogVolumeInterface (l := l) T b).logVolume
        (normalizedComparisonRegion
          (S2586IQHullLogVolumeInterface (l := l) T b)
          (S2588PointMap (l := l) T b) a b c)).toReal ≤
        (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) +
          ((S2586IQHullLogVolumeInterface (l := l) T b).logVolume
            (S2586IQHullLogVolumeInterface (l := l) T b).hull).toReal + D

/-- Constructive bridge: two explicit per-epsilon gap fields give the full
Cor312 -> ABC bridge interface, with carrier the actual qVFam tensor block,
hullData the actual S2586 interface, and logShellPoint the actual S2588 point map. -/
noncomputable def bridgeGapData_toInterface
    (hg : ∀ (epsilon : Real) (heps : 0 < epsilon),
      BridgeGapData (l := l) T b epsilon heps) :
    Cor312ToABCBridgeInterface where
  carrier := qVFamTensorBlock T b
  hullData := S2586IQHullLogVolumeInterface (l := l) T b
  epsilonComparison := fun epsilon heps =>
    { logShellPoint := S2588PointMap (l := l) T b
      height_le_normalizedRegionVolume :=
        (hg epsilon heps).height_le_normalizedRegionVolume
      regionVolume_le_normalizedWeight :=
        (hg epsilon heps).regionVolume_le_normalizedWeight }

/-- The constructed interface's carrier is the actual tensor block. -/
theorem bridgeGapData_toInterface_carrier
    (hg : ∀ (epsilon : Real) (heps : 0 < epsilon),
      BridgeGapData (l := l) T b epsilon heps) :
    (bridgeGapData_toInterface (l := l) T b hg).carrier =
      qVFamTensorBlock T b := rfl

end LeanFormal.IUT.XiFPaper.S2720BridgeSkeletonActualAdapted
end
