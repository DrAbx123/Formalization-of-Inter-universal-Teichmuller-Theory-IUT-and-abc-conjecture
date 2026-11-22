import tmp.sheaf.xif.paper.Mzk1P8HeightInputFinal2Actual
import tmp.sheaf.xif.paper.Mzk1P8GlobalFreyCriterionActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P8ProducerAttempt3Actual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1P8HeightInputActual
open LeanFormal.IUT.XiFPaper.Mzk1P8HeightInputFinal2Actual
open LeanFormal.IUT.XiFPaper.Mzk1P8GlobalFreyCriterionActual

def p8ProducerAttempt3 (D : P8HeightInput) :
    LeanFormal.IUT.XiFPaper.Mzk1P8ActualDisplayHeightActual.P8UniformHeightBound :=
  p8HeightInputFinal2_uniformBound D

theorem p8ProducerAttempt3_nonempty (D : P8HeightInput) :
    Nonempty LeanFormal.IUT.XiFPaper.Mzk1P8ActualDisplayHeightActual.P8UniformHeightBound :=
  ⟨p8ProducerAttempt3 D⟩

end LeanFormal.IUT.XiFPaper.Mzk1P8ProducerAttempt3Actual
end
