import tmp.sheaf.xif.paper.S3128SheafTorsorActual
import tmp.sheaf.xif.paper.S3128FiberTypeActual
import Iut.Foundations.Orbicurve
noncomputable section
open CategoryTheory CategoryTheory.Limits
open Iut
open LeanFormal.IUT.XiFPaper.S3128SheafTorsorActual
open LeanFormal.IUT.XiFPaper.S3128FiberTypeActual
set_option linter.unusedVariables false
namespace LeanFormal.IUT.XiFPaper.S3128QuotientSheafObjActual
variable {F : Type} [Field F] {X : HyperbolicOrbicurve F}

structure S3128ZMod2QuotientSheafObj (U : SchemeOverField F)
    extends S3128ZMod2SheafTorsor (F := F) U where
  mapPoint :
    ∀ V : (Over U)ᵒᵖ,
      points.obj V →
        S3128FiberType (X := X)
          (LocallyDiscrete.mk (Opposite.op V.unop.left))

variable {U U' : SchemeOverField F} (f : U' ⟶ U)

noncomputable def S3128ZMod2QuotientSheafObj.baseChange
    (A : S3128ZMod2QuotientSheafObj (F := F) (X := X) U) :
    S3128ZMod2QuotientSheafObj (F := F) (X := X) U' where
  points := (S3128ZMod2SheafTorsor.baseChange f
    A.toS3128ZMod2SheafTorsor).points
  action := (S3128ZMod2SheafTorsor.baseChange f
    A.toS3128ZMod2SheafTorsor).action
  torsor := (S3128ZMod2SheafTorsor.baseChange f
    A.toS3128ZMod2SheafTorsor).torsor
  mapPoint := by
    intro V p
    exact A.mapPoint ((Over.map f).op.obj V) p

structure S3128ZMod2QuotientSheafHom
    (A B : S3128ZMod2QuotientSheafObj (F := F) (X := X) U) where
  pointsIso : A.points ≅ B.points
  equivariant :
    ∀ g : Multiplicative (ZMod 2),
      pointsIso.hom ≫ B.action g = A.action g ≫ pointsIso.hom
  mapCompat :
    Nonempty
      (∀ (V : (Over U)ᵒᵖ) (p : A.points.obj V),
        B.mapPoint V (pointsIso.hom.app V p) ≅ A.mapPoint V p)

namespace S3128ZMod2QuotientSheafHom
variable {A B C : S3128ZMod2QuotientSheafObj (F := F) (X := X) U}

@[ext] theorem ext (f g : S3128ZMod2QuotientSheafHom A B)
    (h : f.pointsIso = g.pointsIso) : f = g := by
  cases f with
  | mk fi fe fm =>
    cases g with
    | mk gi ge gm =>
      cases h
      rfl

noncomputable def id (A : S3128ZMod2QuotientSheafObj (F := F) (X := X) U) :
    S3128ZMod2QuotientSheafHom A A where
  pointsIso := Iso.refl A.points
  equivariant := by intro g; simp
  mapCompat := ⟨fun V p => Iso.refl _⟩

noncomputable def comp (f : S3128ZMod2QuotientSheafHom A B)
    (g : S3128ZMod2QuotientSheafHom B C) :
    S3128ZMod2QuotientSheafHom A C where
  pointsIso := f.pointsIso.trans g.pointsIso
  equivariant := by
    intro h; rw [Iso.trans_hom]; calc
      (f.pointsIso.hom ≫ g.pointsIso.hom) ≫ C.action h
          = f.pointsIso.hom ≫ (g.pointsIso.hom ≫ C.action h) := Category.assoc _ _ _
      _ = f.pointsIso.hom ≫ (B.action h ≫ g.pointsIso.hom) := by rw [g.equivariant]
      _ = (f.pointsIso.hom ≫ B.action h) ≫ g.pointsIso.hom := (Category.assoc _ _ _).symm
      _ = (A.action h ≫ f.pointsIso.hom) ≫ g.pointsIso.hom := by rw [f.equivariant]
      _ = A.action h ≫ (f.pointsIso.hom ≫ g.pointsIso.hom) := Category.assoc _ _ _
  mapCompat := by
    obtain ⟨fm⟩ := f.mapCompat; obtain ⟨gm⟩ := g.mapCompat
    exact ⟨fun V p => (gm V (f.pointsIso.hom.app V p)).trans (fm V p)⟩

end S3128ZMod2QuotientSheafHom

noncomputable instance S3128ZMod2QuotientSheafCategory :
    Category (S3128ZMod2QuotientSheafObj (F := F) (X := X) U) where
  Hom := S3128ZMod2QuotientSheafHom
  id := S3128ZMod2QuotientSheafHom.id
  comp := S3128ZMod2QuotientSheafHom.comp
  id_comp f := by apply S3128ZMod2QuotientSheafHom.ext; exact Iso.refl_trans f.pointsIso
  comp_id f := by apply S3128ZMod2QuotientSheafHom.ext; exact Iso.trans_refl f.pointsIso
  assoc f g h := by apply S3128ZMod2QuotientSheafHom.ext; exact Iso.trans_assoc f.pointsIso g.pointsIso h.pointsIso

#check S3128ZMod2QuotientSheafObj
#check S3128ZMod2QuotientSheafCategory

end LeanFormal.IUT.XiFPaper.S3128QuotientSheafObjActual