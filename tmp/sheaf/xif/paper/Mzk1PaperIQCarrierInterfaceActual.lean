/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.C3LogShellTensorPacketActual
import LeanFormal.IUT.IUTI.InitialTheta.SourcePlacePartitionReduction
import Mathlib.Tactic
/-! # GAP/interface: paper IQ carrier realization -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1PaperIQCarrierInterfaceActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source LeanFormal.IUT.Theorem311Source.OriginalInput
universe u
variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
structure PaperIQCarrierData where
  carrier : Submodule ℚ (C3LogShellTensorBlock C3)
  carrier_eq : carrier = actualC3LogShellTensorIQ C3
theorem carrier_mem_region (D : PaperIQCarrierData (C3 := C3)) :
    (D.carrier : Set (C3LogShellTensorBlock C3)) =
      actualC3LogShellTensorIQ C3 := by
  rw [D.carrier_eq]
def PaperIQCarrierDataRequired : Prop := Nonempty (PaperIQCarrierData (C3 := C3))
def rows : List String := ["carrier", "carrier_eq actual IQ", "inhabitant NOT constructed"]
theorem rows_length : rows.length = 3 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1PaperIQCarrierInterfaceActual
end