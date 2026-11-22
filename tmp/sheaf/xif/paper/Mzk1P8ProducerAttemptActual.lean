import tmp.sheaf.xif.paper.Mzk1P8HeightInputFinalActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P8ProducerAttemptActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1P8HeightInputActual
open LeanFormal.IUT.XiFPaper.Mzk1P8HeightInputFinalActual

/-- Actual P8 producer from accepted P6/P7/display inputs: produces the
uniform height bound from the height/weight input. -/
def p8ProducerAttempt (D : P8HeightInput) :
    LeanFormal.IUT.XiFPaper.Mzk1P8GlobalFreyCriterionActual.P8UniformHeightBound :=
  p8HeightInputFinal_uniformBound D

theorem p8ProducerAttempt_nonempty
    (D : P8HeightInput) :
    Nonempty LeanFormal.IUT.XiFPaper.Mzk1P8GlobalFreyCriterionActual.P8UniformHeightBound :=
  ⟨p8ProducerAttempt D⟩

end LeanFormal.IUT.XiFPaper.Mzk1P8ProducerAttemptActual
end
