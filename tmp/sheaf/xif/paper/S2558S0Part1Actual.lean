import Mathlib

noncomputable section
set_option maxHeartbeats 8000000
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2558S0Part1Actual

/-- Coefficients 81..160 of the quotient S0. -/
def S0_1 : (ZMod 613)[X] := C 240 * X ^ 81 + C 573 * X ^ 82 + C 118 * X ^ 83 + C 491 * X ^ 84 + C 112 * X ^ 85 + C 556 * X ^ 86 + C 112 * X ^ 87 + C 294 * X ^ 88 + C 564 * X ^ 89 + C 216 * X ^ 90 + C 245 * X ^ 91 + C 6 * X ^ 92 + C 208 * X ^ 93 + C 204 * X ^ 94 + C 477 * X ^ 95 + C 533 * X ^ 96 + C 72 * X ^ 97 + C 84 * X ^ 98 + C 238 * X ^ 99 + C 259 * X ^ 100 + C 506 * X ^ 101 + C 391 * X ^ 102 + C 459 * X ^ 103 + C 486 * X ^ 104 + C 280 * X ^ 105 + C 331 * X ^ 106 + C 499 * X ^ 107 + C 504 * X ^ 108 + C 68 * X ^ 109 + C 520 * X ^ 110 + C 436 * X ^ 111 + C 217 * X ^ 112 + C 226 * X ^ 113 + C 471 * X ^ 114 + C 604 * X ^ 115 + C 442 * X ^ 116 + C 217 * X ^ 117 + C 197 * X ^ 118 + C 553 * X ^ 119 + C 192 * X ^ 120 + C 83 * X ^ 121 + C 100 * X ^ 122 + C 319 * X ^ 123 + C 116 * X ^ 124 + C 256 * X ^ 125 + C 444 * X ^ 126 + C 168 * X ^ 127 + C 336 * X ^ 128 + C 383 * X ^ 129 + C 463 * X ^ 130 + C 115 * X ^ 131 + C 570 * X ^ 132 + C 516 * X ^ 133 + C 62 * X ^ 134 + C 29 * X ^ 135 + C 45 * X ^ 136 + C 127 * X ^ 137 + C 353 * X ^ 138 + C 128 * X ^ 139 + C 479 * X ^ 140 + C 218 * X ^ 141 + C 474 * X ^ 142 + C 570 * X ^ 143 + C 441 * X ^ 144 + C 530 * X ^ 145 + C 449 * X ^ 146 + C 26 * X ^ 147 + C 371 * X ^ 148 + C 345 * X ^ 149 + C 547 * X ^ 150 + C 485 * X ^ 151 + C 184 * X ^ 152 + C 501 * X ^ 153 + C 518 * X ^ 154 + C 612 * X ^ 155 + C 107 * X ^ 156 + C 253 * X ^ 157 + C 483 * X ^ 158 + C 21 * X ^ 159 + C 363 * X ^ 160

theorem S0_1_natDegree_le : S0_1.natDegree ≤ 160 := by
  unfold S0_1
  compute_degree!

end LeanFormal.IUT.XiFPaper.S2558S0Part1Actual

end