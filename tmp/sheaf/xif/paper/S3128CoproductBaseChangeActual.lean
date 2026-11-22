import tmp.sheaf.xif.paper.S3128ZMod2BaseChangeTorsorActual
noncomputable section
open CategoryTheory CategoryTheory.Limits
open Iut
open LeanFormal.IUT.XiFPaper.S3128ZMod2FiberCategoryActual
open LeanFormal.IUT.XiFPaper.S3128ZMod2BaseChangeActual
open LeanFormal.IUT.XiFPaper.S3128ZMod2BaseChangeTorsorActual
set_option linter.unusedVariables false
namespace LeanFormal.IUT.XiFPaper.S3128CoproductBaseChangeActual
variable {F : Type} [Field F] {X : HyperbolicOrbicurve F}
variable {U U' : SchemeOverField F} (f : U' ⟶ U)
variable (A : S3128ZMod2FiberObj (F := F) X U)

/-- The projection `P ⨿ P → U`. -/
abbrev S3128CoproductProj : (A.P ⨿ A.P) ⟶ U :=
  coprod.desc A.proj A.proj

/-- The base change `(P ⨿ P) ×_U U'`. -/
abbrev S3128CoproductBaseChangeObj : SchemeOverField F :=
  pullback (S3128CoproductProj A) f

theorem S3128CoproductProj_inl :
    coprod.inl ≫ S3128CoproductProj A = A.proj := by
  simp only [S3128CoproductProj, coprod.inl_desc]

theorem S3128CoproductProj_inr :
    coprod.inr ≫ S3128CoproductProj A = A.proj := by
  simp only [S3128CoproductProj, coprod.inr_desc]

noncomputable def S3128CoproductBaseChangeMapZero :
    S3128BaseChangeP' f A ⟶ S3128CoproductBaseChangeObj f A :=
  pullback.lift
    (S3128BaseChangeToP f A ≫ coprod.inl)
    (S3128BaseChangeProj f A)
    (by
      rw [Category.assoc, S3128CoproductProj_inl]
      exact pullback.condition)

noncomputable def S3128CoproductBaseChangeMapOne :
    S3128BaseChangeP' f A ⟶ S3128CoproductBaseChangeObj f A :=
  pullback.lift
    (S3128BaseChangeToP f A ≫ coprod.inr)
    (S3128BaseChangeProj f A)
    (by
      rw [Category.assoc, S3128CoproductProj_inr]
      exact pullback.condition)

noncomputable def S3128CoproductBaseChangeMap :
    S3128BaseChangeP' f A ⨿ S3128BaseChangeP' f A ⟶
      S3128CoproductBaseChangeObj f A :=
  coprod.desc
    (S3128CoproductBaseChangeMapZero f A)
    (S3128CoproductBaseChangeMapOne f A)

def S3128CoproductBaseChangeIsoTarget : Prop :=
  IsIso (S3128CoproductBaseChangeMap f A)


#check S3128CoproductBaseChangeObj
#check S3128CoproductBaseChangeMap
#check S3128CoproductBaseChangeIsoTarget

end LeanFormal.IUT.XiFPaper.S3128CoproductBaseChangeActual