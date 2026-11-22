/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.S2717Cor312FullTargetActual
import tmp.sheaf.n8.closure.NativeC1PaperSource
import Mathlib.Tactic
/-! # GAP: packet PActual input vs actual donor C3 input -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1PaperQPilotActualInputMismatchActual
open LeanFormal.IUT LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S2717Cor312FullTargetActual
structure InputRow where
  item : String
  status : String
def inputRows : List InputRow :=
  [ ⟨"QPilotLineActualConstruction.P.input", "OriginalInput l (NativePlaces P.X.S)"⟩,
    ⟨"S2717C3 target input", "OriginalInput l (FinitePrimePlace 2 7) = S2711I R ..."⟩,
    ⟨"direct equality", "NOT proved; V types differ"⟩,
    ⟨"PActual at S2711I", "needs analogous NativeC1PaperSource/C1 at S2711I"⟩ ]
theorem inputRows_length : inputRows.length = 4 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1PaperQPilotActualInputMismatchActual
end