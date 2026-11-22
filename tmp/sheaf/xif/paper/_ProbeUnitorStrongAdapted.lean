import Mathlib
open CategoryTheory
open scoped Pseudofunctor.StrongTrans
namespace ProbeUnitorStrong
variable {B : Type*} [Bicategory B] {C : Type*} [Bicategory C]
variable {F G : Pseudofunctor B C} (η : F.StrongTrans G)
noncomputable def vcompIdIso :
    @Iso (F.StrongTrans G) (Pseudofunctor.StrongTrans.homCategory (F := F) (G := G))
      ((Pseudofunctor.StrongTrans.id F).vcomp η) η :=
  Pseudofunctor.StrongTrans.isoMk (fun a => Bicategory.leftUnitor (η.app a)) (by
    intro a b f
    cat_disch)
#check vcompIdIso
end ProbeUnitorStrong