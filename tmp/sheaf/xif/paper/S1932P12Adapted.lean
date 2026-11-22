import tmp.sheaf.xif.paper.S1932P11

noncomputable section
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace S1932P12Adapted
open CategoryTheory
open CategoryTheory.Bicategory
open AlgebraicGeometry
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1898EllipticInvolutionActual

noncomputable def sqNatTrans (U : LocallyDiscrete (Iut.SchemeOverField S1726K)ᵒᵖ) :
    ((Pseudofunctor.StrongTrans.vcomp S1932P11.Sigma S1932P11.Sigma).app U).toFunctor ⟶
      ((Pseudofunctor.StrongTrans.id S1898Stack).app U).toFunctor where
  app P := eqToHom (by rw [S1932P11.sigmaSq_obj, S1932P11.idApp_obj])
  naturality X Y f := by
    haveI : IsDiscrete (S1898Stack.obj U : Type) := Discrete.isDiscrete _
    exact Subsingleton.elim _ _

end S1932P12Adapted
end
