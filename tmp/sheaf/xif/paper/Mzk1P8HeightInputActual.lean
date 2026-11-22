import tmp.sheaf.xif.paper.Mzk1P8FromP6IVInequalityActual
import tmp.sheaf.xif.paper.Mzk1P7LargeImageCyclicActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P8HeightInputActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1P8FromP6IVInequalityActual
open LeanFormal.IUT.XiFPaper.Mzk1P7LargeImageCyclicActual

/-- Actual P8 height input: P6 IV/paper height bound plus P7 archimedean
height data. -/
structure P8HeightInput where
  p6IVPaperBound : P8P6IVInequalityInput
  p7Arch : P7LargeImageCyclicData 0

/-- Actual input constructor. -/
def p8HeightInputOf (h : P8P6IVInequalityInput) : P8HeightInput where
  p6IVPaperBound := h
  p7Arch := p7LargeImageCyclicData 0

/-- Actual ABC consumer from the P8 height input. -/
theorem p8HeightInput_abcConsumer (D : P8HeightInput) : ABCConjecture :=
  abcConjecture_of_p6IVInequality D.p6IVPaperBound

end LeanFormal.IUT.XiFPaper.Mzk1P8HeightInputActual
end
