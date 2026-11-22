import Mathlib.NumberTheory.Padics.PadicIntegers
#check ZMod.val
#check fun (u : (ZMod 8)ˣ) => ZMod.val (u : ZMod 8)
#check fun (u : (ZMod 8)ˣ) => ((u : ZMod 8)).val
#check fun (u : (ZMod 8)ˣ) => (u : ZMod 8).val
#check fun (u : (ZMod 8)ˣ) => (ZMod.val (u : ZMod 8) : ℕ)
example (u : (ZMod 8)ˣ) : (7 : ZMod 8) ^ (ZMod.val (u : ZMod 8)) = 1 := by decide
