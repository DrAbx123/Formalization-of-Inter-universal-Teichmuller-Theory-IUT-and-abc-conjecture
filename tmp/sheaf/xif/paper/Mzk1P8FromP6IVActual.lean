import tmp.sheaf.xif.paper.Mzk1P8UniformHeightActual
import tmp.sheaf.xif.paper.Mzk1P6StepVBoundConsumerActual
import tmp.sheaf.xif.paper.Mzk1P8ActualDisplayHeightActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P8FromP6IVActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110Actual
open LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual
open LeanFormal.IUT.XiFPaper.Mzk1P8ActualDisplayHeightActual
open LeanFormal.IUT.XiFPaper.Mzk1P8UniformHeightActual
open LeanFormal.IUT.XiFPaper.Mzk1P6StepVBoundConsumerActual

/-- Actual P8-from-P6/IV data: accepted P6 StepV/Thm110 display layer,
P8 actual display terms, and the P8 uniform-height criterion data. -/
structure P8FromP6IVData (A : ActualThm110Data) (c : ℝ) where
  displayTerms : Thm110DisplayTerms
  displayTerms_eq : displayTerms = p8ActualDisplayTerms A
  criterionData : P8UniformHeightCriterionData A c

/-- Actual construction from the P8 display/uniform criterion data. -/
def p8FromP6IVData (A : ActualThm110Data) (c : ℝ) :
    P8FromP6IVData A c where
  displayTerms := p8ActualDisplayTerms A
  displayTerms_eq := rfl
  criterionData := p8UniformHeightCriterionData A c

theorem p8FromP6IVData_nonempty (A : ActualThm110Data) (c : ℝ) :
    Nonempty (P8FromP6IVData A c) :=
  ⟨p8FromP6IVData A c⟩

/-- Actual P8 display slack from the P6/Thm110 Cor312 input. -/
theorem p8FromP6IV_displaySlack (A : ActualThm110Data)
    (hCor312 : thm110Lhs A.toTerms ≤ thm110Mid A.toTerms + thm110Cor312Gap A.toTerms) :
    thm110Lhs (p8ActualDisplayTerms A) ≤ thm110Rhs (p8ActualDisplayTerms A) :=
  p8ActualDisplayTerms_slack A hCor312

/-- Actual P8 uniform height consumer from the assembled P6/IV data. -/
theorem p8FromP6IV_abcConsumer (A : ActualThm110Data) (c : ℝ)
    (D : P8FromP6IVData A c) (h : P8UniformHeightBound) : ABCConjecture :=
  p8UniformHeight_consumer h

/-- Combined actual consumer: P6/IV display slack and uniform height => ABC. -/
theorem p8FromP6IV_combined (A : ActualThm110Data) (c : ℝ)
    (D : P8FromP6IVData A c)
    (hCor312 : thm110Lhs A.toTerms ≤ thm110Mid A.toTerms + thm110Cor312Gap A.toTerms)
    (h : P8UniformHeightBound) :
    thm110Lhs (p8ActualDisplayTerms A) ≤ thm110Rhs (p8ActualDisplayTerms A) ∧
      ABCConjecture :=
  ⟨p8FromP6IV_displaySlack A hCor312, p8FromP6IV_abcConsumer A c D h⟩

end LeanFormal.IUT.XiFPaper.Mzk1P8FromP6IVActual
end
