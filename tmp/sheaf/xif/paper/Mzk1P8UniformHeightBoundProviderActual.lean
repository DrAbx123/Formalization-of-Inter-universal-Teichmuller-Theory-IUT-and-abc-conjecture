import tmp.sheaf.xif.paper.Mzk1P8UniformHeightBoundActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P8UniformHeightBoundProviderActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1P8ActualDisplayHeightActual
open LeanFormal.IUT.XiFPaper.Mzk1P8GlobalFreyCriterionActual
open LeanFormal.IUT.XiFPaper.Mzk1P8UniformHeightBoundActual

/-- Attempted actual unconditional P8 uniform height bound from P6/P7/display
data.  The missing arithmetic estimate is the IUT-IV Cor 3.12-to-ABC estimate. -/
theorem p8UniformHeightBoundActual :
    LeanFormal.IUT.XiFPaper.Mzk1P8ActualDisplayHeightActual.P8UniformHeightBound := by
  intro epsilon hepsilon
  exact ?_

end LeanFormal.IUT.XiFPaper.Mzk1P8UniformHeightBoundProviderActual
end
