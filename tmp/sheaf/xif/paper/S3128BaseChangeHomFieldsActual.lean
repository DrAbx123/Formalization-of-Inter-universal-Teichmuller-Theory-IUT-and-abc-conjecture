import tmp.sheaf.xif.paper.S3128BaseChangeHomActual
import tmp.sheaf.xif.paper.S3128ZMod2BaseChangeObjActual
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT.XiFPaper.S3128ZMod2FiberCategoryActual
open LeanFormal.IUT.XiFPaper.S3128ZMod2FiberEquivariantActual
open LeanFormal.IUT.XiFPaper.S3128ZMod2BaseChangeActual
open LeanFormal.IUT.XiFPaper.S3128ZMod2BaseChangeTorsorActual
open LeanFormal.IUT.XiFPaper.S3128ZMod2BaseChangeObjActual
open LeanFormal.IUT.XiFPaper.S3128BaseChangeHomActual
open LeanFormal.IUT.XiFPaper.S3121StrongTransVcompActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
set_option linter.unusedVariables false
namespace LeanFormal.IUT.XiFPaper.S3128BaseChangeHomFieldsActual
variable {F : Type} [Field F] {X : HyperbolicOrbicurve F}
variable {U U' : SchemeOverField F} (f : U' ⟶ U)
variable (A : S3128ZMod2FiberObj (F := F) X U)

structure S3128BaseObjData where
  torsorIso :
    S3128BaseChangeP f A ⨿ S3128BaseChangeP f A ≅
      pullback (S3128BaseChangeProj f A) (S3128BaseChangeProj f A)
  equivariantData : Prop
  equivariantData_proof : equivariantData

noncomputable abbrev S3128BaseChangeObjOfData (D : S3128BaseObjData f A) :
    S3128ZMod2FiberObj X U' :=
  S3128BaseChangeObj f A D.torsorIso
    D.equivariantData D.equivariantData_proof

variable {A B : S3128ZMod2FiberObj (F := F) X U}
variable (φ : S3128ZMod2EquivariantHom A B)
variable (DA : S3128BaseObjData f A) (DB : S3128BaseObjData f B)

theorem S3128BaseChangeIso_hom_fst :
    (S3128BaseChangeIso f φ).hom ≫ pullback.fst B.proj f =
      pullback.fst A.proj f ≫ φ.iso.hom := by
  rw [S3128BaseChangeIso, pullback.lift_fst]

theorem S3128BaseChangeAut_fst (A : S3128ZMod2FiberObj (F := F) X U)
    (g : Multiplicative (ZMod 2)) :
    (S3128BaseChangeZMod2Aut f A g).hom ≫ pullback.fst A.proj f =
      pullback.fst A.proj f ≫
        ((A.zmod2_action g : A.P ≅ A.P)).hom := by
  change S3128BaseChangeZMod2Hom f A g ≫ pullback.fst A.proj f =
    pullback.fst A.proj f ≫
      ((A.zmod2_action g : A.P ≅ A.P)).hom
  rw [S3128BaseChangeZMod2Hom, pullback.lift_fst]

noncomputable def S3128BaseChangeStackMapCompat
    (h : Nonempty
      (Pseudofunctor.StrongTrans.vcomp
        (S1742StrongTransOfHom φ.iso.hom) B.stackMap ≅
          A.stackMap)) :
    Nonempty
      (Pseudofunctor.StrongTrans.vcomp
        (S1742StrongTransOfHom (S3128BaseChangeIso f φ).hom)
        (S3128BaseChangeStackMap f B) ≅
          S3128BaseChangeStackMap f A) := by
  obtain ⟨hφ⟩ := h
  refine ⟨?_⟩
  change
    Pseudofunctor.StrongTrans.vcomp
        (S1742StrongTransOfHom (S3128BaseChangeIso f φ).hom)
        (Pseudofunctor.StrongTrans.vcomp
          (S1742StrongTransOfHom (S3128BaseChangeToP f B))
          B.stackMap)
      ≅
    Pseudofunctor.StrongTrans.vcomp
      (S1742StrongTransOfHom (S3128BaseChangeToP f A))
      A.stackMap
  let e1 :=
    (Pseudofunctor.StrongTrans.associator
      (S1742StrongTransOfHom (S3128BaseChangeIso f φ).hom)
      (S1742StrongTransOfHom (S3128BaseChangeToP f B))
      B.stackMap).symm
  let e2 :=
    eqToIso (congrArg
      (fun m => Pseudofunctor.StrongTrans.vcomp m B.stackMap)
      (S3121StrongTransOfHom_vcomp F
        (S3128BaseChangeIso f φ).hom (S3128BaseChangeToP f B)))
  let e3 :=
    eqToIso (congrArg
      (fun m => Pseudofunctor.StrongTrans.vcomp m B.stackMap)
      (congrArg S1742StrongTransOfHom
        (S3128BaseChangeIso_hom_fst f φ)))
  let e4 :=
    eqToIso (congrArg
      (fun m => Pseudofunctor.StrongTrans.vcomp m B.stackMap)
      (S3121StrongTransOfHom_vcomp F
        (S3128BaseChangeToP f A) φ.iso.hom).symm)
  let e5 :=
    Pseudofunctor.StrongTrans.associator
      (S1742StrongTransOfHom (S3128BaseChangeToP f A))
      (S1742StrongTransOfHom φ.iso.hom) B.stackMap
  let e6 :=
    Bicategory.whiskerLeftIso
      (a := S1742YS (S3128BaseChangeP f A))
      (b := S1742YS A.P) (c := X.stack.fiber)
      (S1742StrongTransOfHom (S3128BaseChangeToP f A)) hφ
  exact e1.trans (e2.trans (e3.trans (e4.trans (e5.trans e6))))

noncomputable def S3128BaseChangeHom
    (hstack :
      Nonempty
        (Pseudofunctor.StrongTrans.vcomp
          (S1742StrongTransOfHom (S3128BaseChangeIso f φ).hom)
          (S3128BaseChangeStackMap f B) ≅
        S3128BaseChangeStackMap f A)) :
    S3128ZMod2EquivariantHom
      (S3128BaseChangeObjOfData f A DA)
      (S3128BaseChangeObjOfData f B DB) where
  iso := S3128BaseChangeIso f φ
  proj_comm := by
    simp [S3128BaseChangeObjOfData, S3128BaseChangeObj,
      S3128BaseChangeIso, pullback.lift_snd]
  equivariant := by
    intro g
    apply pullback.hom_ext
    · calc
        ((S3128BaseChangeIso f φ).hom
            ≫ (S3128BaseChangeZMod2Aut f B g).hom)
            ≫ pullback.fst B.proj f
            = (S3128BaseChangeIso f φ).hom
                ≫ ((S3128BaseChangeZMod2Aut f B g).hom
                    ≫ pullback.fst B.proj f) := Category.assoc _ _ _
        _ = (S3128BaseChangeIso f φ).hom
                ≫ (pullback.fst B.proj f
                    ≫ ((B.zmod2_action g : B.P ≅ B.P)).hom) := by
              rw [S3128BaseChangeAut_fst]
        _ = ((S3128BaseChangeIso f φ).hom
                ≫ pullback.fst B.proj f)
              ≫ ((B.zmod2_action g : B.P ≅ B.P)).hom :=
              (Category.assoc _ _ _).symm
        _ = (pullback.fst A.proj f ≫ φ.iso.hom)
              ≫ ((B.zmod2_action g : B.P ≅ B.P)).hom := by
              rw [S3128BaseChangeIso_hom_fst]
        _ = pullback.fst A.proj f
              ≫ (φ.iso.hom
                  ≫ ((B.zmod2_action g : B.P ≅ B.P)).hom) :=
              Category.assoc _ _ _
        _ = pullback.fst A.proj f
              ≫ (((A.zmod2_action g : A.P ≅ A.P)).hom
                  ≫ φ.iso.hom) := by
              rw [φ.equivariant]
        _ = (pullback.fst A.proj f
              ≫ ((A.zmod2_action g : A.P ≅ A.P)).hom)
              ≫ φ.iso.hom :=
              (Category.assoc _ _ _).symm
        _ = ((S3128BaseChangeZMod2Aut f A g).hom
              ≫ pullback.fst A.proj f)
              ≫ φ.iso.hom := by
              rw [S3128BaseChangeAut_fst]
        _ = (S3128BaseChangeZMod2Aut f A g).hom
              ≫ (pullback.fst A.proj f ≫ φ.iso.hom) :=
              Category.assoc _ _ _
        _ = (S3128BaseChangeZMod2Aut f A g).hom
              ≫ ((S3128BaseChangeIso f φ).hom
                  ≫ pullback.fst B.proj f) := by
              rw [S3128BaseChangeIso_hom_fst]
        _ = ((S3128BaseChangeZMod2Aut f A g).hom
              ≫ (S3128BaseChangeIso f φ).hom)
              ≫ pullback.fst B.proj f :=
              (Category.assoc _ _ _).symm
    · change
        (S3128BaseChangeIso f φ).hom
            ≫ (S3128BaseChangeZMod2Aut f B g).hom
            ≫ pullback.snd B.proj f =
          (S3128BaseChangeZMod2Aut f A g).hom
            ≫ (S3128BaseChangeIso f φ).hom
            ≫ pullback.snd B.proj f
      simp only [S3128BaseChangeIso, S3128BaseChangeZMod2Aut,
        S3128BaseChangeZMod2Hom, pullback.lift_snd]
  stackMap_compat := hstack

noncomputable def S3128BaseChangeHom'
    (f : U' ⟶ U) {A B : S3128ZMod2FiberObj (F := F) X U}
    (φ : S3128ZMod2EquivariantHom A B)
    (DA : S3128BaseObjData f A) (DB : S3128BaseObjData f B) :
    S3128ZMod2EquivariantHom
      (S3128BaseChangeObjOfData f A DA)
      (S3128BaseChangeObjOfData f B DB) :=
  S3128BaseChangeHom f φ DA DB
    (S3128BaseChangeStackMapCompat f φ φ.stackMap_compat)

theorem S3128BaseChangeFunctor_mapId
    (f : U' ⟶ U)
    (D : ∀ A : S3128ZMod2FiberObj (F := F) X U,
      S3128BaseObjData f A)
    (A : S3128ZMod2FiberObj (F := F) X U) :
    S3128BaseChangeHom' f (𝟙 A) (D A) (D A) =
      S3128ZMod2EquivariantHom.id
        (S3128BaseChangeObjOfData f A (D A)) := by
  apply S3128ZMod2EquivariantHom.ext
  apply Iso.ext
  dsimp [S3128ZMod2EquivariantHom.id, S3128BaseChangeHom',
    S3128BaseChangeHom, S3128BaseChangeIso]
  apply pullback.hom_ext
  · rw [Iso.refl_hom, Category.id_comp]
    change pullback.lift
        (pullback.fst A.proj f ≫ 𝟙 A.P)
        (pullback.snd A.proj f) _ ≫ pullback.fst A.proj f =
      pullback.fst A.proj f
    simp [pullback.lift_fst]
  · simp [S3128ZMod2EquivariantHom.id, Iso.refl_hom,
      pullback.lift_snd]

theorem S3128BaseChangeFunctor_mapComp
    (f : U' ⟶ U)
    (D : ∀ A : S3128ZMod2FiberObj (F := F) X U,
      S3128BaseObjData f A)
    {A B C : S3128ZMod2FiberObj (F := F) X U}
    (φ : A ⟶ B) (ψ : B ⟶ C) :
    S3128BaseChangeHom' f (φ ≫ ψ) (D A) (D C) =
      S3128ZMod2EquivariantHom.comp
        (S3128BaseChangeHom' f φ (D A) (D B))
        (S3128BaseChangeHom' f ψ (D B) (D C)) := by
  apply S3128ZMod2EquivariantHom.ext
  apply Iso.ext
  dsimp [S3128ZMod2FiberEquivariantCategory,
    S3128ZMod2EquivariantHom.comp,
    S3128BaseChangeHom', S3128BaseChangeHom,
    S3128BaseChangeIso, Iso.trans_hom]
  apply pullback.hom_ext
  · have hcomp : (φ ≫ ψ).iso.hom =
        φ.iso.hom ≫ ψ.iso.hom := rfl
    simp only [S3128BaseChangeIso, S3128BaseChangeHom',
        S3128BaseChangeHom, Iso.trans_hom,
        pullback.lift_fst_assoc, pullback.lift_fst,
        Category.assoc]
    rw [hcomp]
  · simp only [S3128BaseChangeIso, S3128BaseChangeHom',
        S3128BaseChangeHom, Iso.trans_hom,
        pullback.lift_snd_assoc, pullback.lift_snd,
        Category.assoc]

noncomputable def S3128BaseChangeFunctor
    (f : U' ⟶ U) (D : ∀ A : S3128ZMod2FiberObj (F := F) X U,
      S3128BaseObjData f A) :
    S3128ZMod2FiberObj X U ⥤ S3128ZMod2FiberObj X U' where
  obj A := S3128BaseChangeObjOfData f A (D A)
  map {A B} φ := S3128BaseChangeHom' f φ (D A) (D B)
  map_id := S3128BaseChangeFunctor_mapId f D
  map_comp := S3128BaseChangeFunctor_mapComp f D

#check S3128BaseChangeHom
#check S3128BaseChangeObjOfData
#print axioms S3128BaseChangeStackMapCompat

end LeanFormal.IUT.XiFPaper.S3128BaseChangeHomFieldsActual