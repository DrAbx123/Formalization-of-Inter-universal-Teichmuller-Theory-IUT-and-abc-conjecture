/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1C3S1902BridgeActual
import tmp.sheaf.xif.paper.S1902ActualThetaHullActual
import Mathlib.Tactic

/-! # GAP: C3↔S1902 Haar scaling data (named input, no inhabitant) -/

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1C3S1902HaarScaleDataActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1C3S1902BridgeActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source LeanFormal.IUT.Theorem311Source.OriginalInput
open MeasureTheory
universe u
variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
structure C3S1902HaarScaleData where
  blockEquiv : C3LogShellTensorBlock C3 ≃ S1902Carrier T
  haarScale : Real
  haarScale_pos : 0 < haarScale
  unitMass : Real
def C3S1902HaarScaleDataRequired : Prop := Nonempty (C3S1902HaarScaleData (T := T) C3)
def rows : List String := ["blockEquiv", "haarScale+pos", "unitMass", "inhabitant NOT constructed"]
theorem rows_length : rows.length = 4 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1C3S1902HaarScaleDataActual
end