/- P8 actual displayTerms inhabitant and uniform height-bound interface. -/
import tmp.sheaf.xif.paper.Mzk1IVThm110Actual
import tmp.sheaf.xif.paper.Mzk1P8GlobalFreyCriterionActual
import tmp.sheaf.xif.paper.Mzk1S1IsogenyHeightActual
import tmp.sheaf.xif.paper.Mzk1G1FermatCoverActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P8ActualDisplayHeightActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110Actual
open LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual
open LeanFormal.IUT.XiFPaper.Mzk1P8GlobalFreyCriterionActual
open LeanFormal.IUT.XiFPaper.Mzk1S1IsogenyHeightActual
open LeanFormal.IUT.XiFPaper.Mzk1G1Actual

/-- Actual Thm 1.10 display terms from actual IV data. -/
noncomputable def p8ActualDisplayTerms (A : ActualThm110Data) : Thm110DisplayTerms :=
  A.toTerms

/-- The actual display terms satisfy the Thm 1.10 slack inequality once the
Cor 3.12 input is supplied. -/
theorem p8ActualDisplayTerms_slack (A : ActualThm110Data)
    (hCor312 : thm110Lhs A.toTerms ≤ thm110Mid A.toTerms + thm110Cor312Gap A.toTerms) :
    thm110Lhs (p8ActualDisplayTerms A) ≤ thm110Rhs (p8ActualDisplayTerms A) :=
  thm110_display_of_hCor312 A hCor312

/-- P8 uniform height bound (same as the actual Frey j product criterion). -/
def P8UniformHeightBound : Prop := ABCFreyJProductHeightCriterion

theorem p8UniformHeightBound_iff_abc :
    P8UniformHeightBound ↔ ABCConjecture :=
  p8_finalCriterion

theorem p8_abc_of_uniformHeightBound_actual
    (h : P8UniformHeightBound) : ABCConjecture :=
  p8UniformHeightBound_iff_abc.mp h

/-- Actual display terms plus uniform bound interface packaged as the P8 node
output. -/
theorem p8_node_actualDisplay_and_uniformBound
    (A : ActualThm110Data)
    (hCor312 : thm110Lhs A.toTerms ≤ thm110Mid A.toTerms + thm110Cor312Gap A.toTerms)
    (h : P8UniformHeightBound) :
    thm110Lhs (p8ActualDisplayTerms A) ≤ thm110Rhs (p8ActualDisplayTerms A) ∧
      ABCConjecture :=
  ⟨p8ActualDisplayTerms_slack A hCor312, p8_abc_of_uniformHeightBound_actual h⟩


/-- Actual P8 global data inhabitant built from actual S1 isogeny-height data,
the actual G1 Fermat cover, and actual Thm 1.10 display terms. -/
theorem p8ActualGlobalData_nonempty (c : ℝ) (A : ActualThm110Data) :
    Nonempty (P8ActualGlobalData c) :=
  ⟨{ isogenyHeight := s1IsogenyHeightActual c
     fermatCover := fermatCoverData ℂ 1 (by norm_num)
     displayTerms := p8ActualDisplayTerms A }⟩

#check p8ActualDisplayTerms
#check p8ActualDisplayTerms_slack
#check p8UniformHeightBound_iff_abc
#check p8_node_actualDisplay_and_uniformBound
#check p8ActualGlobalData_nonempty

end LeanFormal.IUT.XiFPaper.Mzk1P8ActualDisplayHeightActual
end
