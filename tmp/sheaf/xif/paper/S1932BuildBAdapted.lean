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

/-- The componentwise 2-cell `Sigma ; Sigma -> 1` on the underlying functors. -/
noncomputable def S1932SqNatTrans (U : LocallyDiscrete (Iut.SchemeOverField S1726K)ᵒᵖ) :
    ((Pseudofunctor.StrongTrans.vcomp S1932Sigma S1932Sigma).app U).toFunctor ⟶
      ((Pseudofunctor.StrongTrans.id S1898Stack).app U).toFunctor where
  app P := eqToHom (by
    rw [S1932SigmaSq_obj, S1932IdApp_obj]
    apply Discrete.ext
    exact S1932Sq_point U P)
  naturality X Y f := by
    haveI : IsDiscrete (S1898Stack.obj U : Type) := Discrete.isDiscrete _
    exact Subsingleton.elim _ _

/-- The reverse componentwise 2-cell. -/
noncomputable def S1932SqNatTransRev (U : LocallyDiscrete (Iut.SchemeOverField S1726K)ᵒᵖ) :
    ((Pseudofunctor.StrongTrans.id S1898Stack).app U).toFunctor ⟶
      ((Pseudofunctor.StrongTrans.vcomp S1932Sigma S1932Sigma).app U).toFunctor where
  app P := eqToHom (by
    rw [S1932SigmaSq_obj, S1932IdApp_obj]
    apply Discrete.ext
    exact (S1932Sq_point U P).symm)
  naturality X Y f := by
    haveI : IsDiscrete (S1898Stack.obj U : Type) := Discrete.isDiscrete _
    exact Subsingleton.elim _ _

/-- The 2-cell `Sigma ; Sigma -> 1`. -/
noncomputable def S1932SqMod :
    Pseudofunctor.StrongTrans.vcomp S1932Sigma S1932Sigma ⟶
      Pseudofunctor.StrongTrans.id S1898Stack where
  as := {
    app U := NatTrans.toCatHom₂ (S1932SqNatTrans U)
    naturality a b f := by
      exact (S1932NatTransSubsingleton (Discrete.isDiscrete _) _ _).elim _ _ }

/-- The reverse 2-cell `1 -> Sigma ; Sigma`. -/
noncomputable def S1932SqModRev :
    Pseudofunctor.StrongTrans.id S1898Stack ⟶
      Pseudofunctor.StrongTrans.vcomp S1932Sigma S1932Sigma where
  as := {
    app U := NatTrans.toCatHom₂ (S1932SqNatTransRev U)
    naturality a b f := by
      exact (S1932NatTransSubsingleton (Discrete.isDiscrete _) _ _).elim _ _ }

/-- **The square of the actual elliptic involution is the identity.** -/
noncomputable def S1932SigmaSqIso :
    Pseudofunctor.StrongTrans.vcomp S1932Sigma S1932Sigma ≅
      Pseudofunctor.StrongTrans.id S1898Stack :=
  Iso.mk S1932SqMod S1932SqModRev
    (S1932StrongTransSubsingleton _ _).elim _ _
    (S1932StrongTransSubsingleton _ _).elim _ _

end LeanFormal.IUT.XiFPaper.S1932SignActionQuotientActual

end
