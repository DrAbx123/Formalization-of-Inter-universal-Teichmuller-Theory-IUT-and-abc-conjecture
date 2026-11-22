import tmp.sheaf.xif.paper.S1932BuildA

noncomputable section
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.S1932SignActionQuotientActual

open CategoryTheory
open CategoryTheory.Bicategory
open AlgebraicGeometry
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1898EllipticInvolutionActual

/-! ## 3. The square of the actual involution -/

/-- The actual `[-1]` endomorphism of the S1726 stack, as a strong
transformation. -/
abbrev S1932Sigma : Pseudofunctor.StrongTrans S1898Stack S1898Stack :=
  S1898EllipticInvolutionHom

theorem S1932SigmaSq_obj (U : LocallyDiscrete (Iut.SchemeOverField S1726K)ᵒᵖ)
    (P : Discrete (Opposite.unop U.as ⟶ S1726AffineOver)) :
    (((Pseudofunctor.StrongTrans.vcomp S1932Sigma S1932Sigma).app U).toFunctor.obj P) =
      Discrete.mk ((P.as ≫ S1898AffineEndo) ≫ S1898AffineEndo) := rfl

theorem S1932IdApp_obj (U : LocallyDiscrete (Iut.SchemeOverField S1726K)ᵒᵖ)
    (P : Discrete (Opposite.unop U.as ⟶ S1726AffineOver)) :
    ((Pseudofunctor.StrongTrans.id S1898Stack).app U).toFunctor.obj P = P := rfl

theorem S1932Sq_point (U : LocallyDiscrete (Iut.SchemeOverField S1726K)ᵒᵖ)
    (P : Discrete (Opposite.unop U.as ⟶ S1726AffineOver)) :
    (P.as ≫ S1898AffineEndo) ≫ S1898AffineEndo = P.as := by
  rw [Category.assoc, S1932AffineEndo_comp, Category.comp_id]



end LeanFormal.IUT.XiFPaper.S1932SignActionQuotientActual

end
