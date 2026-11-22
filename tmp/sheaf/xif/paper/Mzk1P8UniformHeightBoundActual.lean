import tmp.sheaf.xif.paper.Mzk1P8UniformHeightActual
import tmp.sheaf.xif.paper.Mzk1P8GlobalFreyCriterionActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P8UniformHeightBoundActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1P8ActualDisplayHeightActual
open LeanFormal.IUT.XiFPaper.Mzk1P8GlobalFreyCriterionActual
open LeanFormal.IUT.XiFPaper.Mzk1P8UniformHeightActual
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110Actual
open LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual

/-- Actual P8 uniform height-bound package: the assembled P8 criterion data
(actual display terms + P6 presentation + P7 height data) together with the
uniform Frey j-height bound. -/
structure P8UniformHeightBoundData (A : ActualThm110Data) (c : ℝ) where
  criterionData : P8UniformHeightCriterionData A c
  bound : P8UniformHeightBound

/-- Actual constructor from the assembled P8 data and the uniform bound. -/
def p8UniformHeightBoundData (A : ActualThm110Data) (c : ℝ)
    (h : P8UniformHeightBound) : P8UniformHeightBoundData A c where
  criterionData := p8UniformHeightCriterionData A c
  bound := h

/-- Actual consumer: the packaged P8 data plus uniform bound gives ABC. -/
theorem p8UniformHeightBoundData_consumer
    (A : ActualThm110Data) (c : ℝ) (D : P8UniformHeightBoundData A c) :
    ABCConjecture :=
  p8UniformHeight_consumer D.bound

/-- Actual criterion equivalence retained at the bound level. -/
theorem p8UniformHeightBound_iff_ABC :
    P8UniformHeightBound ↔ ABCConjecture :=
  p8UniformHeightBound_iff_abc

/-- Actual display-slack plus bound consumer using the assembled data. -/
theorem p8UniformHeightBoundData_display_consumer
    (A : ActualThm110Data) (c : ℝ) (D : P8UniformHeightBoundData A c)
    (hCor312 : thm110Lhs A.toTerms ≤ thm110Mid A.toTerms + thm110Cor312Gap A.toTerms) :
    thm110Lhs (p8ActualDisplayTerms A) ≤ thm110Rhs (p8ActualDisplayTerms A) ∧
      ABCConjecture :=
  p8UniformHeight_display_consumer A hCor312 D.bound

end LeanFormal.IUT.XiFPaper.Mzk1P8UniformHeightBoundActual
end
