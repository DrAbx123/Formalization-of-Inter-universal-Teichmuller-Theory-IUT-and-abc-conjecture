import tmp.sheaf.xif.paper.Mzk1P8HeightInputFinal3Actual
import tmp.sheaf.xif.paper.Mzk1P8GlobalFreyCriterionActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P8ProducerAttempt4Actual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1P8HeightInputActual
open LeanFormal.IUT.XiFPaper.Mzk1P8HeightInputFinal3Actual
open LeanFormal.IUT.XiFPaper.Mzk1P8GlobalFreyCriterionActual

def p8ProducerAttempt4 (D : P8HeightInput) :
    LeanFormal.IUT.XiFPaper.Mzk1P8ActualDisplayHeightActual.P8UniformHeightBound :=
  p8HeightInputFinal3_uniformBound D

theorem p8ProducerAttempt4_nonempty (D : P8HeightInput) :
    Nonempty LeanFormal.IUT.XiFPaper.Mzk1P8ActualDisplayHeightActual.P8UniformHeightBound :=
  ⟨p8ProducerAttempt4 D⟩

end LeanFormal.IUT.XiFPaper.Mzk1P8ProducerAttempt4Actual
end
