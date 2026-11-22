import Mathlib
open Polynomial
example (a b c : (ZMod 613)[X]) : a - c - (b - c) = a - b := sub_sub_sub_cancel_right a b c
