import tmp.sheaf.xif.paper.Mzk1P8HeightInputActual
import tmp.sheaf.xif.paper.Mzk1P8HeightInputFinalActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P8ProducerAttempt2Actual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1P8HeightInputActual
open LeanFormal.IUT.XiFPaper.Mzk1P8HeightInputFinalActual

/-- Actual P8 producer attempt 2: from accepted P6/P7 height input,
produce the uniform height bound through the final input consumer. -/
def p8ProducerAttempt2 (D : P8HeightInput) :
    LeanFormal.IUT.XiFPaper.Mzk1P8GlobalFreyCriterionActual.P8UniformHeightBound :=
  p8HeightInputFinal_uniformBound D

theorem p8ProducerAttempt2_nonempty (D : P8HeightInput) :
    Nonempty LeanFormal.IUT.XiFPaper.Mzk1P8GlobalFreyCriterionActual.P8UniformHeightBound :=
  ⟨p8ProducerAttempt2 D⟩

end LeanFormal.IUT.XiFPaper.Mzk1P8ProducerAttempt2Actual
end
