/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1C3DIndexDataActual
import tmp.sheaf.xif.paper.Mzk1C3DictionaryRowsActual
import Mathlib.Tactic
/-! # GAP: C3DIndexData <-> dictionary row statuses (named data) -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1C3DDictionaryAssemblyActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.Mzk1C3DIndexDataActual
open LeanFormal.IUT.XiFPaper.Mzk1C3DictionaryRowsActual
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source LeanFormal.IUT.Theorem311Source.OriginalInput
universe u
variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
def rowStatuses : List (String × String) :=
  [("p", "not proved"), ("place", "not proved"), ("q", "not proved"),
   ("tensorIndex", "no equivalence"), ("tensorPlaces", "no equivalence"),
   ("tensorTuple", "no equivalence")]
theorem rowStatuses_length : rowStatuses.length = 6 := rfl
theorem no_discharged_status :
    rowStatuses.all (fun x => x.2 = "proved") = false := rfl
theorem indexEquiv_bijective (D : C3DIndexData (C3 := C3)) :
    Function.Bijective D.indexEquiv := D.indexEquiv.bijective
def rows : List String := ["p", "place", "q", "tensorIndex", "tensorPlaces", "tensorTuple"]
theorem rows_length : rows.length = 6 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1C3DDictionaryAssemblyActual
end