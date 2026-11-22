import tmp.sheaf.xif.paper.S2429CompositeAssemblyActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
namespace M

example {Y1 Y2 Y3 : EtaleStackPseudofunctor S1726K}
    {f f' : Pseudofunctor.StrongTrans Y1 Y2} (e : Iso f f')
    (h : Pseudofunctor.StrongTrans Y2 Y3) :
    Iso (Pseudofunctor.StrongTrans.vcomp f h) (Pseudofunctor.StrongTrans.vcomp f' h) := by
  let Bicat := EtaleStackPseudofunctor S1726K
  letI : Bicategory Bicat := inferInstance
  let a : Bicat := Y1
  let b : Bicat := Y2
  let c : Bicat := Y3
  let ff : a ⟶ b := f
  let ff' : a ⟶ b := f'
  let hh : b ⟶ c := h
  let ee : ff ≅ ff' := e
  exact @Bicategory.whiskerRightIso Bicat _ a b c ff ff' ee hh

end M
end
