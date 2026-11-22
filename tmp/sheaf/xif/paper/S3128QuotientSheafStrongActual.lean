import tmp.sheaf.xif.paper.S3128QuotientSheafObjActual
noncomputable section
open CategoryTheory CategoryTheory.Limits
open Iut
open LeanFormal.IUT.XiFPaper.S3128SheafTorsorActual
open LeanFormal.IUT.XiFPaper.S3128QuotientSheafObjActual
open LeanFormal.IUT.XiFPaper.S3128FiberTypeActual
set_option linter.unusedVariables false
namespace LeanFormal.IUT.XiFPaper.S3128QuotientSheafStrongActual
variable {F : Type} [Field F] {X : HyperbolicOrbicurve F}
variable {U : SchemeOverField F}

structure S3128StrongHom
    (A B : S3128ZMod2QuotientSheafObj (F := F) (X := X) U) where
  pointsIso : A.points ≅ B.points
  equivariant :
    ∀ g : Multiplicative (ZMod 2),
      pointsIso.hom ≫ B.action g = A.action g ≫ pointsIso.hom
  mapCompat :
    ∀ (V : (Over U)ᵒᵖ) (p : A.points.obj V),
      let L := LocallyDiscrete.mk (Opposite.op V.unop.left)
      (B.mapPoint V (pointsIso.hom.app V p) : S3128FiberType (X := X) L) ≅
        (A.mapPoint V p : S3128FiberType (X := X) L)

namespace S3128StrongHom
variable {A B C : S3128ZMod2QuotientSheafObj (F := F) (X := X) U}

@[ext] theorem ext (f g : S3128StrongHom A B)
    (h : f.pointsIso = g.pointsIso)
    (hm : HEq f.mapCompat g.mapCompat) : f = g := by
  cases f with
  | mk fi fe fm =>
    cases g with
    | mk gi ge gm =>
      cases h
      have hmm : fm = gm := eq_of_heq hm
      cases hmm
      rfl

noncomputable def id (A : S3128ZMod2QuotientSheafObj (F := F) (X := X) U) :
    S3128StrongHom A A where
  pointsIso := Iso.refl A.points
  equivariant := by intro g; simp
  mapCompat := by
    intro V p
    dsimp only
    change A.mapPoint V p ≅ A.mapPoint V p
    exact Iso.refl _

noncomputable def comp (f : S3128StrongHom A B) (g : S3128StrongHom B C) :
    S3128StrongHom A C where
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
    intro V p
    dsimp only
    exact (g.mapCompat V (f.pointsIso.hom.app V p)).trans (f.mapCompat V p)

end S3128StrongHom

noncomputable instance S3128StrongCategory :
    Category (S3128ZMod2QuotientSheafObj (F := F) (X := X) U) where
  Hom := S3128StrongHom
  id := S3128StrongHom.id
  comp := S3128StrongHom.comp
  id_comp f := by
    apply S3128StrongHom.ext
    · exact Iso.refl_trans f.pointsIso
    · apply heq_of_eq
      funext V p
      dsimp only
      apply Iso.ext
      change ((f.mapCompat V p).hom ≫ 𝟙 _) = (f.mapCompat V p).hom
      simp
  comp_id f := by
    apply S3128StrongHom.ext
    · exact Iso.trans_refl f.pointsIso
    · apply heq_of_eq
      funext V p
      dsimp only
      apply Iso.ext
      change (𝟙 _ ≫ (f.mapCompat V p).hom) = (f.mapCompat V p).hom
      simp
  assoc f g h := by
    apply S3128StrongHom.ext
    · exact Iso.trans_assoc f.pointsIso g.pointsIso h.pointsIso
    · apply heq_of_eq
      funext V p
      apply Iso.ext
      change
        (h.mapCompat V
            ((ConcreteCategory.hom (g.pointsIso.hom.app V))
              ((ConcreteCategory.hom (f.pointsIso.hom.app V)) p))
          ≪≫
            ((g.mapCompat V
                ((ConcreteCategory.hom (f.pointsIso.hom.app V)) p))
              ≪≫ f.mapCompat V p)).hom
        =
        (((h.mapCompat V
              ((ConcreteCategory.hom (g.pointsIso.hom.app V))
                ((ConcreteCategory.hom (f.pointsIso.hom.app V)) p)))
            ≪≫ g.mapCompat V
              ((ConcreteCategory.hom (f.pointsIso.hom.app V)) p))
          ≪≫ f.mapCompat V p).hom
      simp [Iso.trans_hom, NatTrans.comp_app, Category.assoc]

#check S3128StrongHom

end LeanFormal.IUT.XiFPaper.S3128QuotientSheafStrongActual