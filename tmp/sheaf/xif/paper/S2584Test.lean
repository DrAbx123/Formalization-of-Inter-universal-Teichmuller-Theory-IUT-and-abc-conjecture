import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Polynomial.Basic

open Polynomial

def R10c : (ZMod 1249)[X] :=
  C 91 + C 1214 * X + C 319 * X^2 + C 805 * X^3 + C 483 * X^4 +
  C 435 * X^5 + C 1242 * X^6 + C 371 * X^7 + C 124 * X^8 + C 193 * X^9

def R7c : (ZMod 1249)[X] :=
  C 933 + C 976 * X + C 1083 * X^2 + C 1020 * X^3 + C 954 * X^4 +
  C 30 * X^5 + C 223 * X^6 + C 46 * X^7 + C 498 * X^8 + C 892 * X^9

def P1c : (ZMod 1249)[X] :=
  C 1220 + C 1205 * X + C 1059 * X^2 + C 718 * X^3 + C 467 * X^4 +
  C 434 * X^5 + C 1206 * X^6 + C 1159 * X^7 + C 1145 * X^8 +
  C 514 * X^9 + C 617 * X^10 + C 80 * X^11 + C 622 * X^12 +
  C 953 * X^13 + C 390 * X^14 + C 1188 * X^15 + C 633 * X^16 +
  C 637 * X^17 + C 1043 * X^18

theorem test : P1c = R10c * R7c := by ring_nf

#print axioms test
