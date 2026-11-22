import tmp.sheaf.xif.paper.S1831StrongSquareGeometricActual
import Mathlib.AlgebraicGeometry.Limits

noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open AlgebraicGeometry
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual

abbrev S1845F := S1726K
abbrev S1845T : SchemeOverField S1845F := S1726AffineOver
abbrev S1845P : SchemeOverField S1845F :=
  Over.mk (Limits.coprod.desc S1845T.hom S1845T.hom)
noncomputable def S1845Fold : S1845P ⟶ S1845T :=
  Over.homMk (show Over.left S1845P ⟶ Over.left S1845T from
      Limits.coprod.desc (𝟙 S1845T.left) (𝟙 S1845T.left)) (by
    show Limits.coprod.desc (𝟙 S1845T.left) (𝟙 S1845T.left) ≫ Over.hom S1845T = Over.hom S1845P
    rw [show Over.hom S1845P = Limits.coprod.desc (Over.hom S1845T) (Over.hom S1845T) from rfl]
    rw [Limits.coprod.desc_comp]; simp)
noncomputable def S1845Inl : S1845T ⟶ S1845P :=
  Over.homMk (show Over.left S1845T ⟶ Over.left S1845P from Limits.coprod.inl) (by
    show Limits.coprod.inl ≫ Over.hom S1845P = Over.hom S1845T
    rw [show Over.hom S1845P = Limits.coprod.desc (Over.hom S1845T) (Over.hom S1845T) from rfl]
    rw [Limits.coprod.inl_desc])
theorem S1845Inl_fold : S1845Inl ≫ S1845Fold = 𝟙 S1845T := by
  apply Comma.hom_ext
  · show Limits.coprod.inl ≫ Limits.coprod.desc (𝟙 S1845T.left) (𝟙 S1845T.left) = 𝟙 S1845T.left
    rw [Limits.coprod.inl_desc]
  · apply Subsingleton.elim
noncomputable def S1845FoldStrong :
    Pseudofunctor.StrongTrans (S1742YS (F := S1845F) S1845P) (S1742YS (F := S1845F) S1845T) :=
  S1742StrongTransOfHom S1845Fold
noncomputable def S1845InlStrong :
    Pseudofunctor.StrongTrans (S1742YS (F := S1845F) S1845T) (S1742YS (F := S1845F) S1845P) :=
  S1742StrongTransOfHom S1845Inl

example (a : LocallyDiscrete (SchemeOverField S1845F)ᵒᵖ)
    (P : Opposite.unop a.as ⟶ S1845T) :
    ((S1742StrongTransOfHom S1845Fold).app a).toFunctor.obj
      (((S1742StrongTransOfHom S1845Inl).app a).toFunctor.obj (Discrete.mk P)) = Discrete.mk P := by
  rw [show (S1742StrongTransOfHom S1845Fold).app a = S1742App S1845Fold a from rfl]
  rw [show (S1742StrongTransOfHom S1845Inl).app a = S1742App S1845Inl a from rfl]
  rw [S1742App_obj]
  rw [S1742App_obj]
  apply Discrete.ext
  rw [Category.assoc, S1845Inl_fold, Category.comp_id]
