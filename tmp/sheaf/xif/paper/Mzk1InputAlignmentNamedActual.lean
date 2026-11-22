/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.QPilotObjectActual
import Mathlib.Tactic
/-! # GAP: OriginalInput alignment named data + PActual transport -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1InputAlignmentNamedActual
open LeanFormal.IUT LeanFormal.IUT.Theorem311Source LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
universe ua uv upi umon ui uC3 uD3 uM uP
variable {l : PrimeGeFive} {V1 V2 : Type uv}
variable (I1 : OriginalInput.{ua, uv, upi, umon, ui} l V1)
variable (I2 : OriginalInput.{ua, uv, upi, umon, ui} l V2)
structure OriginalInputAlignment
    (I1 : OriginalInput.{ua, uv, upi, umon, ui} l V1)
    (I2 : OriginalInput.{ua, uv, upi, umon, ui} l V2) where
  vEquiv : V1 ≃ V2
  initial_heq : HEq I1.initial I2.initial
  family_index_heq : HEq I1.family.index I2.family.index
  input_heq : HEq I1 I2
def paperQPilotObjectActual_transport
    {V : Type uv} {J1 J2 : OriginalInput.{ua, uv, upi, umon, ui} l V}
    (h : J1 = J2)
    (P : PaperQPilotObjectActual.{ua, uv, upi, umon, ui, uC3, uD3, uM, uP} (I := J1)) :
    PaperQPilotObjectActual.{ua, uv, upi, umon, ui, uC3, uD3, uM, uP} (I := J2) := h ▸ P
def OriginalInputAlignmentRequired : Prop := Nonempty (OriginalInputAlignment I1 I2)
def rows : List String := ["vEquiv", "initial_heq", "family_index_heq", "input_heq", "inhabitant NOT constructed"]
theorem rows_length : rows.length = 5 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1InputAlignmentNamedActual
end