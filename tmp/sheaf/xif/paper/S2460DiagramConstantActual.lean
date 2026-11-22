import tmp.sheaf.xif.paper.S2459InvolutionSquaredActual
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete

noncomputable section
open CategoryTheory Bicategory
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2459InvolutionSquaredActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2460DiagramConstantActual

/-- A first actual pseudofunctor with constant object and constant identity map. -/
noncomputable def S2460Diagram :
    Iut.SignActionIndex ⥤ᵖ Iut.EtaleStackPseudofunctor F :=
  CategoryTheory.pseudofunctorOfIsLocallyDiscrete
    (fun _ => S2482Orbicurve.stack.fiber)
    (fun _ => 𝟙 (S2482Orbicurve.stack.fiber))
    (fun _ => Iso.refl _)
    (fun _ _ => (ρ_ (𝟙 (S2482Orbicurve.stack.fiber))).symm)
    (by cat_disch)
    (by cat_disch)
    (by cat_disch)

#print axioms S2460Diagram

end LeanFormal.IUT.XiFPaper.S2460DiagramConstantActual

end
