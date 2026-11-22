import Mathlib

noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
open Polynomial

example : (2 : ZMod 613) * 5 = 10 := by ring_nf
example : (451 : ZMod 613) * 39 = 425 := by ring_nf
example : (451 : ZMod 613) * 39 = 425 := by norm_num
example : (451 : ZMod 613) * 39 = 425 := by decide
example : (2 * X + 3 : (ZMod 613)[X]) * (5 * X + 7) = 10 * X ^ 2 + 29 * X + 21 := by
  ring_nf
example : (2 * X + 3 : (ZMod 613)[X]) * (5 * X + 7) = 10 * X ^ 2 + 29 * X + 21 := by
  ring_nf
  reduce_mod_char
example : (2 * X + 3 : (ZMod 613)[X]) * (5 * X + 7) = 10 * X ^ 2 + 29 * X + 21 := by
  ring_nf
  norm_num
example : (2 * X + 3 : (ZMod 613)[X]).comp (5 + X : (ZMod 613)[X]) = 13 + 2 * X := by
  simp
  ring_nf
