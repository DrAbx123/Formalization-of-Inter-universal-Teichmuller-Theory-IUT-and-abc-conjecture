/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1C3DIndexDataActual
import Mathlib.Tactic
/-! # GAP: C3D field-level named data -> C3DIndexData (conditional) -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1C3DFieldLevelAssemblyActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.Mzk1C3DIndexDataActual
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source LeanFormal.IUT.Theorem311Source.OriginalInput
universe u
variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
structure C3DFieldLevelData where
  dIndex : Type
  indexEquiv : C3.tensorIndex ≃ dIndex
  dPlaceIndex : dIndex → Type
  dPlaces : (i : dIndex) → dPlaceIndex i → FinitePlaceAtPrime (I.initial.arithmetic.Fmod) C3.p
  dTuple : (i : dIndex) → dPlaceIndex i
  fieldStatus : List (String × String)
def C3DFieldLevelData.toIndexData (D : C3DFieldLevelData (C3 := C3)) :
    C3DIndexData (C3 := C3) where
  dIndex := D.dIndex
  indexEquiv := D.indexEquiv
  dPlaceIndex := D.dPlaceIndex
  dPlaces := D.dPlaces
  dTuple := D.dTuple
theorem toIndexData_indexEquiv (D : C3DFieldLevelData (C3 := C3)) :
    (D.toIndexData).indexEquiv = D.indexEquiv := rfl
def C3DFieldLevelDataRequired : Prop := Nonempty (C3DFieldLevelData (C3 := C3))
def rows : List String := ["indexEquiv", "dPlaceIndex", "dPlaces", "dTuple", "fieldStatus", "inhabitant NOT constructed"]
theorem rows_length : rows.length = 6 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1C3DFieldLevelAssemblyActual
end