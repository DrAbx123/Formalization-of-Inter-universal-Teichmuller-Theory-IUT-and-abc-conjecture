import Mathlib.CategoryTheory.Iso
open CategoryTheory
#check Aut.Aut_inv_def
#check Aut.coe_symm
#check Aut.coe_trans
#check Aut.Aut_mul_def
#check (inferInstance : Group (Aut (Type)))
#check Aut.ext
#check Aut.Aut_one_def