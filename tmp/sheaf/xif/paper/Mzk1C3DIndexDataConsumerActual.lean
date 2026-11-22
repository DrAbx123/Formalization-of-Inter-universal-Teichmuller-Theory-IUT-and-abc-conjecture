/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1C3DIndexDataActual
import Mathlib.Tactic
/-! # GAP: C3DIndexData projections (named data only) -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1C3DIndexDataConsumerActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.Mzk1C3DIndexDataActual
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source LeanFormal.IUT.Theorem311Source.OriginalInput
universe u
variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
def dIndex_equiv (D : C3DIndexData (C3 := C3)) :
    C3.tensorIndex ≃ D.dIndex := D.indexEquiv
def dPlaces_fiber (D : C3DIndexData (C3 := C3)) (i : D.dIndex) :
    D.dPlaceIndex i → FinitePlaceAtPrime (I.initial.arithmetic.Fmod) C3.p := D.dPlaces i
def rows : List String := ["dIndex_equiv", "dPlaces_fiber", "named data only"]
theorem rows_length : rows.length = 3 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1C3DIndexDataConsumerActual
end