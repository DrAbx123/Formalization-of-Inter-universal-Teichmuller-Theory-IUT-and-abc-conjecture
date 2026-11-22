import Mathlib.CategoryTheory.Action
open CategoryTheory
variable {G : Type} [Group G] {X : Type} [MulAction G X]
variable {f g : ActionCategory G X} (η : f ⟶ g)
#check η.val
#check (show G from η.val)
#check (CategoryTheory.SingleObj.toEnd (M := G)).symm η.val
#check congrArg Sigma.snd η.property
