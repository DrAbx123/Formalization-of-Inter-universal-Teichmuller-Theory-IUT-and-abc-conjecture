import Mathlib
open CategoryTheory
#check LocallyDiscrete.comp_def
#check LocallyDiscrete.mk
#check LocallyDiscrete.eq_to_hom
#print LocallyDiscrete
#check CategoryTheory.SingleObj.star
#check Multiplicative.ofAdd
#eval (show (Multiplicative.ofAdd (1:ZMod 2) * Multiplicative.ofAdd (1:ZMod 2)) = 1 from by decide)