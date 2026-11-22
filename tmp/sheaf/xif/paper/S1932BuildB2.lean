import tmp.sheaf.xif.paper.S1932BuildB1

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

/-- The component of the 2-cell `Sigma ; Sigma -> 1` at a point. -/
noncomputable def S1932SqAppFun (U : LocallyDiscrete (Iut.SchemeOverField S1726K)ᵒᵖ)
    (P : Discrete (Opposite.unop U.as ⟶ S1726AffineOver)) :
    ((Pseudofunctor.StrongTrans.vcomp S1932Sigma S1932Sigma).app U).toFunctor.obj P ⟶
      ((Pseudofunctor.StrongTrans.id S1898Stack).app U).toFunctor.obj P :=
  eqToHom (by
    rw [S1932SigmaSq_obj, S1932IdApp_obj]
    apply Discrete.ext
    exact S1932Sq_point U P)

/-- The componentwise 2-cell `Sigma ; Sigma -> 1` on the underlying functors. -/
noncomputable def S1932SqNatTrans (U : LocallyDiscrete (Iut.SchemeOverField S1726K)ᵒᵖ) :
    ((Pseudofunctor.StrongTrans.vcomp S1932Sigma S1932Sigma).app U).toFunctor ⟶
      ((Pseudofunctor.StrongTrans.id S1898Stack).app U).toFunctor where
  app := S1932SqAppFun U
  naturality := by
    intro X Y f
    haveI : IsDiscrete (S1898Stack.obj U : Type) := Discrete.isDiscrete _
    exact Subsingleton.elim _ _

/-- The reverse componentwise 2-cell. -/
noncomputable def S1932SqAppFunRev (U : LocallyDiscrete (Iut.SchemeOverField S1726K)ᵒᵖ)
    (P : Discrete (Opposite.unop U.as ⟶ S1726AffineOver)) :
    ((Pseudofunctor.StrongTrans.id S1898Stack).app U).toFunctor.obj P ⟶
      ((Pseudofunctor.StrongTrans.vcomp S1932Sigma S1932Sigma).app U).toFunctor.obj P :=
  eqToHom (by
    rw [S1932SigmaSq_obj, S1932IdApp_obj]
    apply Discrete.ext
    exact (S1932Sq_point U P).symm)

noncomputable def S1932SqNatTransRev (U : LocallyDiscrete (Iut.SchemeOverField S1726K)ᵒᵖ) :
    ((Pseudofunctor.StrongTrans.id S1898Stack).app U).toFunctor ⟶
      ((Pseudofunctor.StrongTrans.vcomp S1932Sigma S1932Sigma).app U).toFunctor where
  app := S1932SqAppFunRev U
  naturality := by
    intro X Y f
    haveI : IsDiscrete (S1898Stack.obj U : Type) := Discrete.isDiscrete _
    exact Subsingleton.elim _ _

/-- The component 2-cell `Sigma ; Sigma -> 1` at a test object. -/
noncomputable def S1932SqAppCell (U : LocallyDiscrete (Iut.SchemeOverField S1726K)ᵒᵖ) :
    ((Pseudofunctor.StrongTrans.vcomp S1932Sigma S1932Sigma).app U) ⟶
      ((Pseudofunctor.StrongTrans.id S1898Stack).app U) :=
  NatTrans.toCatHom₂ (S1932SqNatTrans U)

noncomputable def S1932SqAppCellRev (U : LocallyDiscrete (Iut.SchemeOverField S1726K)ᵒᵖ) :
    ((Pseudofunctor.StrongTrans.id S1898Stack).app U) ⟶
      ((Pseudofunctor.StrongTrans.vcomp S1932Sigma S1932Sigma).app U) :=
  NatTrans.toCatHom₂ (S1932SqNatTransRev U)

/-- The 2-cell `Sigma ; Sigma -> 1`. -/
noncomputable def S1932SqMod :
    Pseudofunctor.StrongTrans.vcomp S1932Sigma S1932Sigma ⟶
      Pseudofunctor.StrongTrans.id S1898Stack where
  as := {
    app := S1932SqAppCell
    naturality := by
      intro a b f
      exact (S1932NatTransSubsingleton (Y := S1898Stack.obj b) (Discrete.isDiscrete _) _ _).elim _ _ }

/-- The reverse 2-cell `1 -> Sigma ; Sigma`. -/
noncomputable def S1932SqModRev :
    Pseudofunctor.StrongTrans.id S1898Stack ⟶
      Pseudofunctor.StrongTrans.vcomp S1932Sigma S1932Sigma where
  as := {
    app := S1932SqAppCellRev
    naturality := by
      intro a b f
      exact (S1932NatTransSubsingleton (Y := S1898Stack.obj b) (Discrete.isDiscrete _) _ _).elim _ _ }

/-- **The square of the actual elliptic involution is the identity.** -/
noncomputable def S1932SigmaSqIso :
    Pseudofunctor.StrongTrans.vcomp S1932Sigma S1932Sigma ≅
      Pseudofunctor.StrongTrans.id S1898Stack :=
  Iso.mk S1932SqMod S1932SqModRev
    (by exact (S1932StrongTransSubsingleton _ _).elim _ _)
    (by exact (S1932StrongTransSubsingleton _ _).elim _ _)


end LeanFormal.IUT.XiFPaper.S1932SignActionQuotientActual

end
