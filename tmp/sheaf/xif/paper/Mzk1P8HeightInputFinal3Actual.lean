import tmp.sheaf.xif.paper.Mzk1P8HeightInputActual
import tmp.sheaf.xif.paper.Mzk1P8ActualDisplayHeightActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P8HeightInputFinal3Actual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1P8HeightInputActual
open LeanFormal.IUT.XiFPaper.Mzk1P8ActualDisplayHeightActual

theorem p8HeightInputFinal3_abcConsumer (D : P8HeightInput) : ABCConjecture :=
  p8HeightInput_abcConsumer D

def p8HeightInputFinal3_uniformBound (D : P8HeightInput) :
    P8UniformHeightBound :=
  p8UniformHeightBound_iff_abc.mpr (p8HeightInputFinal3_abcConsumer D)

end LeanFormal.IUT.XiFPaper.Mzk1P8HeightInputFinal3Actual
end
