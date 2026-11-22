/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P0NativeQDonorActual
import tmp.sheaf.xif.paper.Mzk1P0NativeReadoutActual
import tmp.sheaf.xif.paper.Mzk1P0NativeTensorConsumerActual
import Mathlib.Tactic
/-! # P0.6: native L-side actual objects (constructed from T, not old concrete L-side) -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0NativeLSideActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.Mzk1P0NativeQDonorActual
open LeanFormal.IUT.XiFPaper.Mzk1P0NativeReadoutActual
open LeanFormal.IUT.XiFPaper.Mzk1P0NativeTensorConsumerActual
open MeasureTheory
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable [Fintype (Bad (nativePlaceSelection T))]
/-- The native L-side tensor block: exactly the qVFam tensor block. -/
abbrev nativeLSideBlock : Type := qVFamTensorBlock T b
/-- The native L-side actual tensor region (local log-shells). -/
noncomputable def nativeLSideRegion : Set (nativeLSideBlock T b) :=
  nativeTensorRegion (p := qVFamTensorP T b)
    (qVFamTensorPlaces T b) (qVFamTensorTuple)
/-- The native L-side tensor log-volume. -/
noncomputable def nativeLSideLogVolume : Real :=
  nativeTensorLogVolume (p := qVFamTensorP T b)
    (qVFamTensorPlaces T b) (qVFamTensorTuple)
/-- The native L-side theta readout: same object as nativeThetaReadout. -/
noncomputable def nativeLSideThetaReadout : Real := nativeLSideLogVolume T b
theorem nativeLSideThetaReadout_eq :
    nativeLSideThetaReadout T b = nativeThetaReadout T b := rfl
/-- The native L-side q readout: uses NativeQDonor q. -/
noncomputable def nativeLSideQReadout : Real := donorQReadout (T := T) (b := b)
theorem nativeLSideQReadout_eq :
    nativeLSideQReadout T b = nativeQReadout T b := rfl
def nativeLComparison : Prop := nativeLSideQReadout T b ≤ nativeLSideThetaReadout T b
theorem nativeLComparison_of_theta_nonneg
    (h : 0 ≤ nativeLSideThetaReadout T b) : nativeLComparison T b :=
  le_trans (nativeQReadout_nonpos T b) h
def rows : List String :=
  ["nativeLSideBlock = qVFamTensorBlock (F-domain)",
   "nativeLSideRegion/Haar/LogVolume = nativeTensor* objects",
   "nativeLSideThetaReadout = nativeThetaReadout rfl",
   "nativeLSideQReadout = nativeQReadout rfl",
   "old concrete-donor L-side files remain historical"]
theorem rows_length : rows.length = 5 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1P0NativeLSideActual
end