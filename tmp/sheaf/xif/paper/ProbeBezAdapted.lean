import Mathlib
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
open Polynomial
namespace ProbeBezAdapted

def G : (ZMod 13)[X] := C 5 + C 11 * X ^ 2 + C 5 * X ^ 3 + C 2 * X ^ 4 + C 5 * X ^ 5 + C 2 * X ^ 7 + C 8 * X ^ 8 + C 5 * X ^ 9 + C 10 * X ^ 10 + C 3 * X ^ 11 + C 1 * X ^ 12
def T4 : (ZMod 13)[X] := C 2 + C 4 * X + C 2 * X ^ 2 + C 9 * X ^ 3 + C 5 * X ^ 4 + C 3 * X ^ 5 + C 12 * X ^ 6 + C 9 * X ^ 7 + C 9 * X ^ 8 + C 4 * X ^ 9 + C 8 * X ^ 10 + C 3 * X ^ 11
def U4 : (ZMod 13)[X] := C 4 + C 3 * X + C 5 * X ^ 2 + C 3 * X ^ 3 + C 10 * X ^ 4 + C 11 * X ^ 5 + C 9 * X ^ 6 + C 5 * X ^ 7 + C 2 * X ^ 8 + C 5 * X ^ 9 + C 8 * X ^ 10
def V4 : (ZMod 13)[X] := C 10 + C 10 * X + C 12 * X ^ 2 + C 10 * X ^ 3 + C 8 * X ^ 4 + C 3 * X ^ 5 + C 1 * X ^ 7 + C 1 * X ^ 8 + C 5 * X ^ 9 + C 9 * X ^ 10 + C 6 * X ^ 11

example : U4 * G + V4 * (T4 - X) = 1 := by
  unfold U4 V4 G T4
  ring_nf
  simp only [← C_mul, ← C_pow]
  norm_num

end ProbeBezAdapted
