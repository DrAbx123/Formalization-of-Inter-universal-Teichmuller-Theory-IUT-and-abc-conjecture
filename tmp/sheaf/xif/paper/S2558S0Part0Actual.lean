import Mathlib

noncomputable section
set_option maxHeartbeats 8000000
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2558S0Part0Actual

/-- The first 81 coefficients of the quotient S0. -/
def S0_0 : (ZMod 613)[X] := C 39 + C 281 * X + C 78 * X ^ 2 + C 265 * X ^ 3 + C 31 * X ^ 4 + C 121 * X ^ 5 + C 82 * X ^ 6 + C 150 * X ^ 7 + C 21 * X ^ 8 + C 336 * X ^ 9 + C 230 * X ^ 10 + C 554 * X ^ 11 + C 455 * X ^ 12 + C 168 * X ^ 13 + C 532 * X ^ 14 + C 32 * X ^ 15 + C 500 * X ^ 16 + C 163 * X ^ 17 + C 586 * X ^ 18 + C 118 * X ^ 19 + C 264 * X ^ 20 + C 560 * X ^ 21 + C 360 * X ^ 22 + C 309 * X ^ 23 + C 168 * X ^ 24 + C 601 * X ^ 25 + C 373 * X ^ 26 + C 288 * X ^ 27 + C 519 * X ^ 28 + C 73 * X ^ 29 + C 567 * X ^ 30 + C 465 * X ^ 31 + C 162 * X ^ 32 + C 370 * X ^ 33 + C 329 * X ^ 34 + C 331 * X ^ 35 + C 157 * X ^ 36 + C 337 * X ^ 37 + C 530 * X ^ 38 + C 236 * X ^ 39 + C 563 * X ^ 40 + C 120 * X ^ 41 + C 108 * X ^ 42 + C 117 * X ^ 43 + C 152 * X ^ 44 + C 368 * X ^ 45 + C 229 * X ^ 46 + C 448 * X ^ 47 + C 481 * X ^ 48 + C 152 * X ^ 49 + C 376 * X ^ 50 + C 161 * X ^ 51 + C 277 * X ^ 52 + C 224 * X ^ 53 + C 296 * X ^ 54 + C 525 * X ^ 55 + C 104 * X ^ 56 + C 92 * X ^ 57 + C 172 * X ^ 58 + C 219 * X ^ 59 + C 51 * X ^ 60 + C 530 * X ^ 61 + C 145 * X ^ 62 + C 520 * X ^ 63 + C 411 * X ^ 64 + C 489 * X ^ 65 + C 430 * X ^ 66 + C 373 * X ^ 67 + C 431 * X ^ 68 + C 240 * X ^ 69 + C 376 * X ^ 70 + C 185 * X ^ 71 + C 505 * X ^ 72 + C 200 * X ^ 73 + C 102 * X ^ 74 + C 60 * X ^ 75 + C 526 * X ^ 76 + C 47 * X ^ 77 + C 487 * X ^ 78 + C 295 * X ^ 79 + C 590 * X ^ 80

theorem S0_0_natDegree_le : S0_0.natDegree ≤ 80 := by
  unfold S0_0
  compute_degree!

end LeanFormal.IUT.XiFPaper.S2558S0Part0Actual

end