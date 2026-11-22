/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1C3DIndexDataActual
import Mathlib.Tactic
/-! # GAP: C3D place/tuple named data -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1C3DPlaceTupleDataActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.Mzk1C3DIndexDataActual
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source LeanFormal.IUT.Theorem311Source.OriginalInput
universe u
variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
structure C3DPlaceTupleData where
  dIndex : Type
  dPlaceIndex : dIndex → Type
  dPlaces : (i : dIndex) → dPlaceIndex i → FinitePlaceAtPrime (I.initial.arithmetic.Fmod) C3.p
  dTuple : (i : dIndex) → dPlaceIndex i
def C3DPlaceTupleDataRequired : Prop := Nonempty (C3DPlaceTupleData (C3 := C3))
def rows : List String := ["dPlaceIndex", "dPlaces", "dTuple", "inhabitant NOT constructed"]
theorem rows_length : rows.length = 4 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1C3DPlaceTupleDataActual
end