/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.n8.closure.C2Actual
import LeanFormal.IUT.IUTIII.Theorem311.SourceOriginalInput
import Mathlib.Tactic
/-! # C2 actual: PActual.line.C2 is constructible from C1 -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1PaperQPilotActualC2ClosedActual
open LeanFormal.IUT LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourceInputBinding
open LeanFormal.IUT.N8Closure.SourceLogKummerRealization
open LeanFormal.IUT.N8Closure.C2Actual
universe u
variable {l : PrimeGeFive} {V : Type}
variable (I : LeanFormal.IUT.Theorem311Source.OriginalInput l V) (C1 : SourceInputBinding I)
def c2Actual : SourceLogKummerData I C1 := sourceLogKummerDataActual I C1
theorem c2Actual_nonempty : Nonempty (SourceLogKummerData I C1) :=
  sourceLogKummerData_nonempty_actual I C1
def rows : List String := ["sourceLogKummerDataActual", "sourceLogKummerData_nonempty_actual", "PActual.line.C2 supplied"]
theorem rows_length : rows.length = 3 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1PaperQPilotActualC2ClosedActual
end