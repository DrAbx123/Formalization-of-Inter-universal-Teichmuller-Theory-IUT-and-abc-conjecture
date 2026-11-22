/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P0NativeSourceCoreActual
import tmp.sheaf.xif.paper.Mzk1P0NativeTensorConsumerActual
import Mathlib.Tactic
/-! # P0: native q/theta readouts (no old C3) -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0NativeReadoutActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.Mzk1P0NativeTensorConsumerActual
open MeasureTheory
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
noncomputable def nativeQReadout : Real :=
  -|Real.log ‖(qVFamily T b).q‖|
theorem nativeQReadout_eq : nativeQReadout T b = -|Real.log ‖(qVFamily T b).q‖| := rfl
theorem nativeQReadout_nonpos : nativeQReadout T b ≤ 0 := by
  unfold nativeQReadout
  exact neg_nonpos.mpr (abs_nonneg _)
noncomputable def nativeThetaReadout : Real :=
  nativeTensorLogVolume (p := qVFamTensorP T b)
    (qVFamTensorPlaces T b) (qVFamTensorTuple)
theorem nativeThetaReadout_eq :
    nativeThetaReadout T b =
      nativeTensorLogVolume (p := qVFamTensorP T b)
        (qVFamTensorPlaces T b) (qVFamTensorTuple) := rfl
def NativeComparison : Prop := nativeQReadout T b ≤ nativeThetaReadout T b
def rows : List String := ["nativeQReadout = -|log q|", "nativeThetaReadout = native tensor logVolume", "NativeComparison (P0 target, not proved)"]
theorem rows_length : rows.length = 3 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1P0NativeReadoutActual
end