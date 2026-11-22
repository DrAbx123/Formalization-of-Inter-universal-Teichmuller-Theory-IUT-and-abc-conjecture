import Mathlib.CategoryTheory.SingleObj
import Mathlib.CategoryTheory.EssentiallySmall
open CategoryTheory
abbrev G := Multiplicative (ZMod 5)
#synth SmallCategory (SingleObj G)
#synth EssentiallySmall (SingleObj G)
