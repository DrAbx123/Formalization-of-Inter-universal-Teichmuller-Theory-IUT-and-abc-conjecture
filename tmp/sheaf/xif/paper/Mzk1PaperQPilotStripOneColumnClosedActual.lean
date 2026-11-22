/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.S1266SourceInd3Actual
import tmp.sheaf.n8.closure.NativeC1PaperSource
import Mathlib.Tactic
/-! # PActual strip closed; oneColumn remains parameter -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1PaperQPilotStripOneColumnClosedActual
open LeanFormal.IUT LeanFormal.IUT.Theorem311Source LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.NativeC1PaperSource
open LeanFormal.IUT.XiFPaper.S1266SourceInd3Actual
open LeanFormal.IUT.N8Closure.NativeInput
variable {l : PrimeGeFive} (P : NativeC1PaperSource l)
def strip : SourceFTimesMuPrimeStrip (NativePlaces P.X.S) := ind3TimesMuStrip (l := l) (V := NativePlaces P.X.S) (I := P.input) 1 0
theorem strip_eq : strip P = ind3TimesMuStrip (l := l) (V := NativePlaces P.X.S) (I := P.input) 1 0 := rfl
def rows : List String := ["strip actual", "oneColumn still parameter (see S366OneColumnActual)"]
theorem rows_length : rows.length = 2 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1PaperQPilotStripOneColumnClosedActual
end