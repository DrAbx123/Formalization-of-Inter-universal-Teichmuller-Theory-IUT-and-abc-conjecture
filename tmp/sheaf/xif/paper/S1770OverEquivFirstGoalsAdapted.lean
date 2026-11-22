import tmp.sheaf.xif.paper.S1768CommutesActual

noncomputable section
open CategoryTheory CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual
open LeanFormal.IUT.XiFPaper.S1755TwoYonedaSmallnessActual
open LeanFormal.IUT.XiFPaper.S1756QuotientActual
open LeanFormal.IUT.XiFPaper.S1761SubsingletonIsoActual
open LeanFormal.IUT.XiFPaper.S1762OverModelHomActual
open LeanFormal.IUT.XiFPaper.S1766WhiskerBridgeActual
open LeanFormal.IUT.XiFPaper.S1767OverToQuotConditionalActual
open LeanFormal.IUT.XiFPaper.S1768CommutesActual
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 12000000

namespace LeanFormal.IUT.XiFPaper.S1770OverEquivFirstGoalsAdapted

variable {A B : S1728Cover}

noncomputable def S1770Equiv :
    S1756CoverMapQuot A B ≃ S1762ModelHomOver A B where
  toFun := S1766QuotToOver A B
  invFun := S1768OverToQuot
  left_inv := by
    intro q
    induction q using Quot.ind with
    | _ f => ?_
  right_inv := by
    intro g
    apply S1762ModelHomOver.ext
    ?_

end LeanFormal.IUT.XiFPaper.S1770OverEquivFirstGoalsAdapted
end
