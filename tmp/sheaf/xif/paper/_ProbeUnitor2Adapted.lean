import Mathlib
open CategoryTheory
open scoped Pseudofunctor.StrongTrans
namespace ProbeUnitor
variable {B : Type*} [Bicategory B] {C : Type*} [Bicategory C]
variable {F G : Pseudofunctor B C} (η : F.StrongTrans G)
example : @Iso (Pseudofunctor.StrongTrans F G) (Pseudofunctor.StrongTrans.homCategory (F := F) (G := G)) ((Pseudofunctor.StrongTrans.id F).vcomp η) η := by
  refine Pseudofunctor.StrongTrans.isoMk (fun a => ?_) ?_
  · exact eqToIso (by rfl)
  · intro a b f
    simp
end ProbeUnitor