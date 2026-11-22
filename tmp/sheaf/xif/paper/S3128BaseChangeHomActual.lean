import tmp.sheaf.xif.paper.S3128ZMod2BaseChangeObjActual
import tmp.sheaf.xif.paper.S3128ZMod2FiberEquivariantActual
noncomputable section
open CategoryTheory CategoryTheory.Limits
open Iut
open LeanFormal.IUT.XiFPaper.S3128ZMod2FiberCategoryActual
open LeanFormal.IUT.XiFPaper.S3128ZMod2FiberEquivariantActual
open LeanFormal.IUT.XiFPaper.S3128ZMod2BaseChangeActual
open LeanFormal.IUT.XiFPaper.S3128ZMod2BaseChangeTorsorActual
set_option linter.unusedVariables false
namespace LeanFormal.IUT.XiFPaper.S3128BaseChangeHomActual
variable {F : Type} [Field F] {X : HyperbolicOrbicurve F}
variable {U U' : SchemeOverField F} (f : U' ⟶ U)
variable {A B : S3128ZMod2FiberObj (F := F) X U}
variable (φ : S3128ZMod2EquivariantHom A B)

/-- Underlying base-change iso on total schemes. -/
noncomputable def S3128BaseChangeIso :
    S3128BaseChangeP f A ≅ S3128BaseChangeP f B where
  hom := pullback.lift
    (pullback.fst A.proj f ≫ φ.iso.hom)
    (pullback.snd A.proj f)
    (by
      rw [Category.assoc, φ.proj_comm, pullback.condition])
  inv := pullback.lift
    (pullback.fst B.proj f ≫ φ.iso.inv)
    (pullback.snd B.proj f)
    (by
      have hinv : φ.iso.inv ≫ A.proj = B.proj := by
        rw [← φ.proj_comm, ← Category.assoc,
          Iso.inv_hom_id, Category.id_comp]
      rw [Category.assoc, hinv, pullback.condition])
  hom_inv_id := by
    apply pullback.hom_ext
    · rw [Category.assoc]
      simp only [S3128BaseChangeP, pullback.lift_fst]
      erw [← Category.assoc]
      rw [pullback.lift_fst]
      rw [Category.assoc]
      rw [Iso.hom_inv_id]
      simp
    · rw [Category.assoc]
      rw [pullback.lift_snd]
      rw [pullback.lift_snd]
      simp
  inv_hom_id := by
    apply pullback.hom_ext
    · rw [Category.assoc]
      simp only [S3128BaseChangeP, pullback.lift_fst]
      erw [← Category.assoc]
      rw [pullback.lift_fst]
      rw [Category.assoc]
      rw [Iso.inv_hom_id]
      simp
    · rw [Category.assoc]
      rw [pullback.lift_snd]
      rw [pullback.lift_snd]
      simp

#check S3128BaseChangeIso
#print axioms S3128BaseChangeIso

end LeanFormal.IUT.XiFPaper.S3128BaseChangeHomActual