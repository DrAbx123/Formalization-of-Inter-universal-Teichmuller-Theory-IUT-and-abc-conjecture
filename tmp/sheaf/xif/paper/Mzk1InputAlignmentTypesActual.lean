/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1PaperQPilotActualInputMismatchActual
import tmp.sheaf.xif.paper.S2711PaperMultiUnconditionalActual
import Mathlib.Tactic
/-! # GAP: precise type table P.input vs S2711I -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1InputAlignmentTypesActual
open LeanFormal.IUT LeanFormal.IUT.Theorem311Source LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.NativeC1PaperSource
open LeanFormal.IUT.XiFPaper.S2711PaperMultiUnconditionalActual
structure AlignTypeRow where
  item : String
  packetInput : String
  s2711Input : String
def typeRows : List AlignTypeRow :=
  [ ⟨"V", "NativePlaces P.X.S (subtype of NumberFieldPlace K)", "FinitePrimePlace 2 7 (subtype of Nat)"⟩,
    ⟨"l", "PrimeGeFive", "S2678PaperUnconditionalHcompActual.fiveLabel"⟩,
    ⟨"input", "OriginalInput l (NativePlaces P.X.S)", "OriginalInput fiveLabel (FinitePrimePlace 2 7)"⟩,
    ⟨"initial", "SourceDefinition31Data l", "SourceDefinition31Data fiveLabel"⟩,
    ⟨"family", "SourceHodgeTheaterFamily l (NativePlaces ...)", "SourceHodgeTheaterFamily fiveLabel (FinitePrimePlace ...)"⟩ ]
theorem typeRows_length : typeRows.length = 5 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1InputAlignmentTypesActual
end