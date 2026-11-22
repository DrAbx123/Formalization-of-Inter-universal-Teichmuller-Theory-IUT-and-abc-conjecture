import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo
import Mathlib.CategoryTheory.Category.Cat
open CategoryTheory
open scoped CategoryTheory.Pseudofunctor.StrongTrans
variable (B : Type) [Category B] (C : Type) [Bicategory C]
#synth Bicategory (Pseudofunctor (LocallyDiscrete B) C)
#check CategoryTheory.Pseudofunctor.StrongTrans.instBicategory
