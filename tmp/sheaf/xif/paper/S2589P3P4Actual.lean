import tmp.sheaf.xif.paper.S2586IQHullLogVolumeInstantiationActual
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface

noncomputable section
open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S2586IQHullLogVolumeInstantiationActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2589P3P4Actual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (β : Bad (nativePlaceSelection T))
variable [MeasurableSpace (qVFamTensorBlock T β)]
variable [BorelSpace (qVFamTensorBlock T β)]

/-- The actual P1 interface on the qVFamTensorBlock carrier. -/
abbrev P3W : IQHullLogVolumeInterface (qVFamTensorBlock T β) :=
  S2586IQHullLogVolumeInterface T β

/-- P3 constant D0: the finite unit-region Haar log-volume. -/
def P3D0 : Real := ((P3W T β).logVolume (P3W T β).unitRegion).toReal

/-- The unit region has finite log-volume (from the actual interface field). -/
theorem P3_unitRegion_logVolume_lt_top :
    (P3W T β).logVolume (P3W T β).unitRegion < ⊤ :=
  (P3W T β).unitRegion_logVolume_lt_top

/-- The hull has finite log-volume, via `rootNormHull_subset_holomorphic` and
the compact canonical unit reference (the S2586 interface field). -/
theorem P3_hull_logVolume_lt_top :
    (P3W T β).logVolume (P3W T β).hull < ⊤ :=
  (P3W T β).hull_logVolume_lt_top

/-- **P3 hunit**, actual on the qVFamTensorBlock P1 carrier:
the unit-region volume is bounded by the hull volume plus the finite unit-region
normalization constant D0. -/
theorem P3_hunit :
    (P3W T β).logVolume (P3W T β).unitRegion <=
      (P3W T β).logVolume (P3W T β).hull + ENNReal.ofReal (P3D0 T β) := by
  unfold P3D0
  rw [ENNReal.ofReal_toReal (ne_of_lt (P3W T β).unitRegion_logVolume_lt_top)]
  calc (P3W T β).logVolume (P3W T β).unitRegion
      = (P3W T β).logVolume (P3W T β).unitRegion + 0 := by rw [add_zero]
    _ ≤ (P3W T β).logVolume (P3W T β).unitRegion +
          (P3W T β).logVolume (P3W T β).hull := by
        exact add_le_add (le_refl ((P3W T β).logVolume (P3W T β).unitRegion))
          (show (0 : ENNReal) ≤ (P3W T β).logVolume (P3W T β).hull from bot_le)
    _ = (P3W T β).logVolume (P3W T β).hull +
          (P3W T β).logVolume (P3W T β).unitRegion := add_comm _ _

/-- The P4 weight-volume dictionary on the actual carrier. -/
def P4WeightVolumeDictionary (p : Nat -> Nat -> Nat -> qVFamTensorBlock T β) : Prop :=
  forall a b c : Nat, IsABCTriple a b c ->
    arithmeticWeight (abcRationalPoint a c) <=
      ((P3W T β).logVolume (normalizedComparisonRegion (P3W T β) p a b c)).toReal

/-- P4 dictionary is exactly the `hweightvol` input of the Cor 3.12 gap assembly. -/
theorem P4_hweightvol_of_dictionary
    (p : Nat -> Nat -> Nat -> qVFamTensorBlock T β)
    (h : P4WeightVolumeDictionary T β p) :
    forall a b c : Nat, IsABCTriple a b c ->
      arithmeticWeight (abcRationalPoint a c) <=
        ((P3W T β).logVolume (normalizedComparisonRegion (P3W T β) p a b c)).toReal :=
  h

#print axioms P3_hunit
#print axioms P4_hweightvol_of_dictionary

end LeanFormal.IUT.XiFPaper.S2589P3P4Actual
end
