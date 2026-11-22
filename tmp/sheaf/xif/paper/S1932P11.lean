import tmp.sheaf.xif.paper.S1898EllipticInvolutionActual

noncomputable section
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace S1932P11
open CategoryTheory
open CategoryTheory.Bicategory
open AlgebraicGeometry
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1898EllipticInvolutionActual

abbrev Sigma : Pseudofunctor.StrongTrans S1898Stack S1898Stack := S1898EllipticInvolutionHom

theorem sigmaSq_obj (U : LocallyDiscrete (Iut.SchemeOverField S1726K)ᵒᵖ)
    (P : Discrete (Opposite.unop U.as ⟶ S1726AffineOver)) :
    (((Pseudofunctor.StrongTrans.vcomp Sigma Sigma).app U).toFunctor.obj P) =
      Discrete.mk ((P.as ≫ S1898AffineEndo) ≫ S1898AffineEndo) := rfl

theorem idApp_obj (U : LocallyDiscrete (Iut.SchemeOverField S1726K)ᵒᵖ)
    (P : Discrete (Opposite.unop U.as ⟶ S1726AffineOver)) :
    ((Pseudofunctor.StrongTrans.id S1898Stack).app U).toFunctor.obj P = P := rfl

end S1932P11
end
