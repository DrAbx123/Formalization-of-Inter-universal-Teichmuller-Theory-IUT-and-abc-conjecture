import tmp.sheaf.xif.paper.S3128ZMod2FiberCategoryActual
import tmp.sheaf.xif.paper.S3121StrongTransVcompActual
noncomputable section
open CategoryTheory CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT.XiFPaper.S3128ZMod2FiberCategoryActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S3121StrongTransVcompActual
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3128ZMod2FiberEquivariantActual

/-- Equivariant isomorphisms of Z/2 fiber objects: projection-compatible,
Z/2-equivariant, and compatible with the SignGroup-equivariant stack maps.
The two compatibility fields are `Prop`s. -/
structure S3128ZMod2EquivariantHom
    {F : Type} [Field F]
    {X : HyperbolicOrbicurve F} {U : SchemeOverField F}
    (A B : S3128ZMod2FiberObj (F := F) X U) where
  iso : A.P ≅ B.P
  proj_comm : iso.hom ≫ B.proj = A.proj
  equivariant :
    ∀ g : Multiplicative (ZMod 2),
      iso.hom ≫ (B.zmod2_action g).hom = (A.zmod2_action g).hom ≫ iso.hom
  stackMap_compat :
    Nonempty
      (Pseudofunctor.StrongTrans.vcomp
        (S1742StrongTransOfHom iso.hom) B.stackMap ≅ A.stackMap)

namespace S3128ZMod2EquivariantHom
variable {F : Type} [Field F]
variable {X : HyperbolicOrbicurve F} {U : SchemeOverField F}
variable {A B C : S3128ZMod2FiberObj (F := F) X U}

@[ext] theorem ext (f g : S3128ZMod2EquivariantHom A B) (h : f.iso = g.iso) :
    f = g := by
  cases f with
  | mk fi fp fe fs =>
    cases g with
    | mk gi gp ge gs =>
      cases h
      rfl

noncomputable def id (A : S3128ZMod2FiberObj (F := F) X U) :
    S3128ZMod2EquivariantHom A A where
  iso := Iso.refl A.P
  proj_comm := by simp
  equivariant := by intro g; simp
  stackMap_compat := by
    refine ⟨?h⟩
    simp only [Iso.refl_hom]
    rw [S3121StrongTransOfHom_id]
    exact Pseudofunctor.StrongTrans.leftUnitor A.stackMap

noncomputable def comp (f : S3128ZMod2EquivariantHom A B)
    (g : S3128ZMod2EquivariantHom B C) :
    S3128ZMod2EquivariantHom A C where
  iso := f.iso.trans g.iso
  proj_comm := by
    rw [Iso.trans_hom, Category.assoc, g.proj_comm, f.proj_comm]
  equivariant := by
    intro h
    rw [Iso.trans_hom]
    calc
      (f.iso.hom ≫ g.iso.hom) ≫ (C.zmod2_action h).hom
          = f.iso.hom ≫ (g.iso.hom ≫ (C.zmod2_action h).hom) :=
            Category.assoc _ _ _
      _ = f.iso.hom ≫ ((B.zmod2_action h).hom ≫ g.iso.hom) :=
            by rw [g.equivariant]
      _ = (f.iso.hom ≫ (B.zmod2_action h).hom) ≫ g.iso.hom :=
            (Category.assoc _ _ _).symm
      _ = ((A.zmod2_action h).hom ≫ f.iso.hom) ≫ g.iso.hom :=
            by rw [f.equivariant]
      _ = (A.zmod2_action h).hom ≫ (f.iso.hom ≫ g.iso.hom) :=
            Category.assoc _ _ _
  stackMap_compat := by
    obtain ⟨gIso⟩ := g.stackMap_compat
    obtain ⟨fIso⟩ := f.stackMap_compat
    let a := S1742StrongTransOfHom f.iso.hom
    let b := S1742StrongTransOfHom g.iso.hom
    let e : Pseudofunctor.StrongTrans.vcomp
        (S1742StrongTransOfHom (f.iso.trans g.iso).hom) C.stackMap ≅
        Pseudofunctor.StrongTrans.vcomp
          (Pseudofunctor.StrongTrans.vcomp a b) C.stackMap := by
      apply eqToIso
      rw [Iso.trans_hom]
      exact congrArg
        (fun t => Pseudofunctor.StrongTrans.vcomp t C.stackMap)
        (S3121StrongTransOfHom_vcomp F f.iso.hom g.iso.hom).symm
    let assoc := Pseudofunctor.StrongTrans.associator a b C.stackMap
    let whisk := Bicategory.whiskerLeftIso
      (a := S1742YS A.P) (b := S1742YS B.P) (c := X.stack.fiber) a gIso
    exact ⟨e.trans (assoc.trans (whisk.trans fIso))⟩

end S3128ZMod2EquivariantHom

noncomputable instance S3128ZMod2FiberEquivariantCategory
    {F : Type} [Field F] (X : HyperbolicOrbicurve F) (U : SchemeOverField F) :
    Category (S3128ZMod2FiberObj X U) where
  Hom := S3128ZMod2EquivariantHom
  id := S3128ZMod2EquivariantHom.id
  comp := S3128ZMod2EquivariantHom.comp
  id_comp f := by
    apply S3128ZMod2EquivariantHom.ext
    exact Iso.refl_trans f.iso
  comp_id f := by
    apply S3128ZMod2EquivariantHom.ext
    exact Iso.trans_refl f.iso
  assoc f g h := by
    apply S3128ZMod2EquivariantHom.ext
    exact Iso.trans_assoc f.iso g.iso h.iso

#check S3128ZMod2EquivariantHom
#check S3128ZMod2EquivariantHom.id
#check S3128ZMod2EquivariantHom.comp
#check S3128ZMod2FiberEquivariantCategory

end LeanFormal.IUT.XiFPaper.S3128ZMod2FiberEquivariantActual