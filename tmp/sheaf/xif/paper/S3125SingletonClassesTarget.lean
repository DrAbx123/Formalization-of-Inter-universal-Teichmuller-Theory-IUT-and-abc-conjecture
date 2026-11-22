import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Pseudo
import Mathlib.CategoryTheory.Bicategory.Modification.Pseudo

noncomputable section
open CategoryTheory
open scoped Pseudofunctor.StrongTrans
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1600000

namespace LeanFormal.IUT.XiFPaper.S3125SingletonClassesTarget

universe u v w

variable {B : Type u} [Bicategory.{w, v} B]
variable {C : Type*} [Bicategory C]
variable {F G : Pseudofunctor B C}

abbrev S3125CommutesTwoCell (eta theta : F ⟶ G) : Type _ :=
  Pseudofunctor.StrongTrans.Hom eta theta

theorem S3125_modification_subsingleton {eta theta : F ⟶ G}
    (h : forall b : B, Subsingleton (eta.app b ⟶ theta.app b)) :
    Subsingleton (Pseudofunctor.StrongTrans.Modification eta theta) := by
  constructor
  intro m n
  apply Pseudofunctor.StrongTrans.Modification.ext
  funext b
  exact Subsingleton.elim _ _

theorem S3125_twoCell_subsingleton {eta theta : F ⟶ G}
    (h : forall b : B, Subsingleton (eta.app b ⟶ theta.app b)) :
    Subsingleton (S3125CommutesTwoCell eta theta) := by
  constructor
  intro m n
  ext b
  exact Subsingleton.elim _ _

#check S3125CommutesTwoCell
#check S3125_modification_subsingleton
#check S3125_twoCell_subsingleton
#print axioms S3125_modification_subsingleton
#print axioms S3125_twoCell_subsingleton

end LeanFormal.IUT.XiFPaper.S3125SingletonClassesTarget
end