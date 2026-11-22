/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1InputAlignmentNamedActual
import Mathlib.Tactic
/-! # GAP: input alignment composite (named alignment only) -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1InputAlignmentCompositeActual
open LeanFormal.IUT LeanFormal.IUT.Theorem311Source LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.XiFPaper.Mzk1InputAlignmentNamedActual
universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable (I1 I2 : OriginalInput.{ua, uv, upi, umon, ui} l V)
structure AlignedPActualData where
  align : OriginalInputAlignment I1 I2
  input_eq : I1 = I2
theorem alignedPActualData_input_eq (A : AlignedPActualData (I1 := I1) (I2 := I2)) :
    I1 = I2 := A.input_eq
def rows : List String := ["align", "input_eq", "PActual source/target transport remains GAP (cross-V cast)", "actual P inhabitant is Mzk1PaperQPilotActualInhabitantOfPacketActual (green)"]
theorem rows_length : rows.length = 4 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1InputAlignmentCompositeActual
end