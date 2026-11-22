import tmp.sheaf.xif.paper.Mzk1P8ActualDisplayHeightActual
import tmp.sheaf.xif.paper.Mzk1P7LargeImageCyclicActual
import tmp.sheaf.xif.paper.Mzk1P6ActualProducersActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P8UniformHeightActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110Actual
open LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual
open LeanFormal.IUT.XiFPaper.Mzk1P8ActualDisplayHeightActual
open LeanFormal.IUT.XiFPaper.Mzk1P7LargeImageCyclicActual
open LeanFormal.IUT.XiFPaper.Mzk1P6ActualProducersActual

/-- Actual P8 uniform-height criterion data: the actual Thm 1.10 display terms,
the P6 display-term presentation, and the P7 archimedean/large-image height
data. -/
structure P8UniformHeightCriterionData (A : ActualThm110Data) (c : ℝ) where
  displayTerms : Thm110DisplayTerms
  displayTerms_eq : displayTerms = p8ActualDisplayTerms A
  p6Terms : Thm110DisplayTerms
  p6Terms_eq : p6Terms = p8ActualDisplayTerms A
  p7Height : P7LargeImageCyclicData c

/-- Actual construction from the actual display terms and actual P7 height
data. -/
def p8UniformHeightCriterionData (A : ActualThm110Data) (c : ℝ) :
    P8UniformHeightCriterionData A c where
  displayTerms := p8ActualDisplayTerms A
  displayTerms_eq := rfl
  p6Terms := p8ActualDisplayTerms A
  p6Terms_eq := rfl
  p7Height := p7LargeImageCyclicData c

theorem p8UniformHeightCriterionData_nonempty (A : ActualThm110Data) (c : ℝ) :
    Nonempty (P8UniformHeightCriterionData A c) :=
  ⟨p8UniformHeightCriterionData A c⟩

/-- Actual P8 uniform height-bound consumer: the P8 uniform height criterion
implies the ABC conjecture. -/
theorem p8UniformHeight_consumer
    (h : P8UniformHeightBound) : ABCConjecture :=
  p8_abc_of_uniformHeightBound_actual h

/-- Actual combined consumer: display slack plus the P8 uniform height bound. -/
theorem p8UniformHeight_display_consumer
    (A : ActualThm110Data)
    (hCor312 : thm110Lhs A.toTerms ≤ thm110Mid A.toTerms + thm110Cor312Gap A.toTerms)
    (h : P8UniformHeightBound) :
    thm110Lhs (p8ActualDisplayTerms A) ≤ thm110Rhs (p8ActualDisplayTerms A) ∧
      ABCConjecture :=
  p8_node_actualDisplay_and_uniformBound A hCor312 h

/-- Actual consumer from the assembled P8 data plus the uniform height bound. -/
theorem p8UniformHeightCriterionData_consumer
    (A : ActualThm110Data) (c : ℝ)
    (D : P8UniformHeightCriterionData A c)
    (h : P8UniformHeightBound) : ABCConjecture :=
  p8UniformHeight_consumer h

end LeanFormal.IUT.XiFPaper.Mzk1P8UniformHeightActual
end
