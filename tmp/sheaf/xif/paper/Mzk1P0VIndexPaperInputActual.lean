/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P0PaperInputActual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0VIndexPaperInputActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.XiFPaper.Mzk1P0PaperInputActual
variable {l : PrimeGeFive}
structure P05PaperInputStrip (P : P05PaperInput l) where
  vIndex : NativePlaces P.X.S ≃ FinitePrimePlace 2 7
def rows : List String := ["V-strip equivalence as paper input field", "not constructed from T", "or use X with V=FinitePrimePlace 2 7"]
theorem rows_length : rows.length = 3 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1P0VIndexPaperInputActual
end
