import tmp.sheaf.xif.paper.Mzk1P8HeightInputActual
import tmp.sheaf.xif.paper.Mzk1P8ActualDisplayHeightActual
import tmp.sheaf.xif.paper.Mzk1P8GlobalFreyCriterionActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P8HeightInputFinalActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1P8HeightInputActual
open LeanFormal.IUT.XiFPaper.Mzk1P8GlobalFreyCriterionActual
open LeanFormal.IUT.XiFPaper.Mzk1P8ActualDisplayHeightActual

/-- Actual final P8 height input consumer: the P6 IV/paper height bound and
P7 archimedean data give ABC. -/
theorem p8HeightInputFinal_abcConsumer (D : P8HeightInput) : ABCConjecture :=
  p8HeightInput_abcConsumer D

/-- Actual P8 uniform height bound produced from the final input. -/
def p8HeightInputFinal_uniformBound (D : P8HeightInput) : P8UniformHeightBound :=
  p8UniformHeightBound_iff_abc.mpr (p8HeightInputFinal_abcConsumer D)

end LeanFormal.IUT.XiFPaper.Mzk1P8HeightInputFinalActual
end
