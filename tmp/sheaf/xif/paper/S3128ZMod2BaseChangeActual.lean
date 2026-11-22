import tmp.sheaf.xif.paper.S3128ZMod2FiberEquivariantActual
import Mathlib.AlgebraicGeometry.Pullbacks
noncomputable section
open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT.XiFPaper.S3128ZMod2FiberCategoryActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3128ZMod2BaseChangeActual
variable {F : Type} [Field F] {X : HyperbolicOrbicurve F}
variable {U U' : SchemeOverField F} (f : U' ⟶ U)
variable (A : S3128ZMod2FiberObj (F := F) X U)

/-- Base-change carrier: pullback of the torsor projection along `f`. -/
abbrev S3128BaseChangeP : SchemeOverField F :=
  pullback A.proj f

/-- New projection to the test object. -/
abbrev S3128BaseChangeProj : S3128BaseChangeP f A ⟶ U' :=
  pullback.snd A.proj f

/-- Comparison morphism back to the original torsor. -/
abbrev S3128BaseChangeToP : S3128BaseChangeP f A ⟶ A.P :=
  pullback.fst A.proj f

/-- Pulled-back equivariant stack map. -/
noncomputable def S3128BaseChangeStackMap :
    Pseudofunctor.StrongTrans
      (S1742YS (S3128BaseChangeP f A)) X.stack.fiber :=
  Pseudofunctor.StrongTrans.vcomp
    (S1742StrongTransOfHom (S3128BaseChangeToP f A)) A.stackMap

/-- Forward arrow on the pullback induced by a Z/2-action element. -/
noncomputable def S3128BaseChangeZMod2Hom (g : Multiplicative (ZMod 2)) :
    S3128BaseChangeP f A ⟶ S3128BaseChangeP f A :=
  pullback.lift
    (pullback.fst A.proj f ≫ (A.zmod2_action g).hom)
    (pullback.snd A.proj f)
    (by
      rw [Category.assoc, A.action_proj g, pullback.condition])


abbrev S3128BaseChangeAutHom (g : Multiplicative (ZMod 2)) : A.P ⟶ A.P :=
  ((A.zmod2_action g : A.P ≅ A.P)).hom

theorem S3128BaseChangeZMod2Hom_hcomp (g : Multiplicative (ZMod 2)) :
    S3128BaseChangeAutHom A g ≫ S3128BaseChangeAutHom A g⁻¹ = 𝟙 A.P := by
  have h := congrArg
    (fun e : CategoryTheory.Aut A.P => ((e : A.P ≅ A.P)).hom)
    (map_mul (A.zmod2_action) g⁻¹ g)
  rw [CategoryTheory.Aut.Aut_mul_def, Iso.trans_hom] at h
  have hg : g⁻¹ * g = 1 := inv_mul_cancel g
  rw [hg, map_one] at h
  have hone : (Iso.hom (1 : CategoryTheory.Aut A.P) : A.P ⟶ A.P) = 𝟙 A.P := rfl
  rw [hone] at h
  simpa [S3128BaseChangeAutHom] using h.symm



noncomputable def S3128BaseChangeZMod2Aut (g : Multiplicative (ZMod 2)) :
    CategoryTheory.Aut (S3128BaseChangeP f A) where
  hom := S3128BaseChangeZMod2Hom f A g
  inv := S3128BaseChangeZMod2Hom f A g⁻¹
  hom_inv_id := by
    apply pullback.hom_ext
    · simp only [Category.id_comp]
      rw [Category.assoc]
      simp only [S3128BaseChangeZMod2Hom]
      rw [pullback.lift_fst]
      erw [← Category.assoc]
      rw [pullback.lift_fst]
      rw [Category.assoc]
      rw [S3128BaseChangeZMod2Hom_hcomp]
      simp
    · simp only [Category.id_comp]
      rw [Category.assoc]
      simp only [S3128BaseChangeZMod2Hom]
      rw [pullback.lift_snd]
      rw [pullback.lift_snd]
  inv_hom_id := by
    apply pullback.hom_ext
    · simp only [Category.id_comp]
      rw [Category.assoc]
      simp only [S3128BaseChangeZMod2Hom]
      rw [pullback.lift_fst]
      erw [← Category.assoc]
      rw [pullback.lift_fst]
      rw [Category.assoc]
      change pullback.fst A.proj f ≫
        (S3128BaseChangeAutHom A g⁻¹ ≫ S3128BaseChangeAutHom A g) = pullback.fst A.proj f
      rw [show S3128BaseChangeAutHom A g⁻¹ ≫ S3128BaseChangeAutHom A g = 𝟙 A.P from by
        simpa using S3128BaseChangeZMod2Hom_hcomp A g⁻¹]
      simp
    · simp only [Category.id_comp]
      rw [Category.assoc]
      simp only [S3128BaseChangeZMod2Hom]
      rw [pullback.lift_snd]
      rw [pullback.lift_snd]

#check S3128BaseChangeZMod2Aut
#print axioms S3128BaseChangeZMod2Aut




noncomputable def S3128BaseChangeZMod2Action :
    Multiplicative (ZMod 2) →* CategoryTheory.Aut (S3128BaseChangeP f A) where
  toFun := S3128BaseChangeZMod2Aut f A
  map_one' := by
    apply CategoryTheory.Aut.ext
    change S3128BaseChangeZMod2Hom f A 1 = 𝟙 (S3128BaseChangeP f A)
    apply pullback.hom_ext
    · rw [S3128BaseChangeZMod2Hom, pullback.lift_fst, map_one A.zmod2_action]
      change pullback.fst A.proj f ≫ 𝟙 A.P =
        𝟙 (S3128BaseChangeP f A) ≫ pullback.fst A.proj f
      simp
    · rw [S3128BaseChangeZMod2Hom, pullback.lift_snd]
      simp
  map_mul' := by
    intro g h
    apply CategoryTheory.Aut.ext
    change S3128BaseChangeZMod2Hom f A (g * h) =
      S3128BaseChangeZMod2Hom f A h ≫ S3128BaseChangeZMod2Hom f A g
    apply pullback.hom_ext
    · simp only [S3128BaseChangeZMod2Hom]
      rw [pullback.lift_fst]
      rw [Category.assoc]
      rw [pullback.lift_fst]
      erw [← Category.assoc]
      rw [pullback.lift_fst]
      rw [Category.assoc]
      simp only [Category.assoc, map_mul A.zmod2_action,
        CategoryTheory.Aut.Aut_mul_def, Iso.trans_hom]
    · simp only [S3128BaseChangeZMod2Hom, pullback.lift_snd,
        pullback.lift_snd_assoc, Category.assoc]

#check S3128BaseChangeZMod2Action
#print axioms S3128BaseChangeZMod2Action

#check S3128BaseChangeP
#check S3128BaseChangeProj
#check S3128BaseChangeToP
#check S3128BaseChangeStackMap
#check S3128BaseChangeZMod2Hom

end LeanFormal.IUT.XiFPaper.S3128ZMod2BaseChangeActual