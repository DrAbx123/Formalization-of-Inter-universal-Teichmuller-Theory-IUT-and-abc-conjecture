import Mathlib
open Polynomial
noncomputable section
opaque P4 : (ZMod 613)[X] := (X : (ZMod 613)[X]) ^ (613 ^ 4)
example : P4 = (X : (ZMod 613)[X]) ^ (613 ^ 4) := by unfold P4
end
