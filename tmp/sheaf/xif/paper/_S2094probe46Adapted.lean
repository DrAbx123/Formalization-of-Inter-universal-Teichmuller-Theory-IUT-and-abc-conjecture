import Mathlib

open Polynomial

local instance : Fact (Nat.Prime 29) := ⟨by norm_num⟩

noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

def f : (ZMod 29)[X] :=
  monomial 0 10 + monomial 1 24 + monomial 2 16 + monomial 3 14 + monomial 4 24 +
  monomial 5 8 + monomial 6 5 + monomial 7 7 + monomial 8 0 + monomial 9 25 + monomial 10 1

def P1 : (ZMod 29)[X] :=
  monomial 0 13 + monomial 1 1 + monomial 2 26 + monomial 3 24 + monomial 4 4 +
  monomial 5 10 + monomial 6 25 + monomial 7 23 + monomial 8 18 + monomial 9 20

def Q1 : (ZMod 29)[X] :=
  monomial 0 19 + monomial 1 21 + monomial 2 21 + monomial 3 3 + monomial 4 23 +
  monomial 5 18 + monomial 6 28 + monomial 7 16 + monomial 8 10 + monomial 9 13 +
  monomial 10 7 + monomial 11 8 + monomial 12 6 + monomial 13 24 + monomial 14 2 +
  monomial 15 21 + monomial 16 28 + monomial 17 16 + monomial 18 4 + monomial 19 1

lemma hdeg_prod : (f * Q1).natDegree = 29 := by
  unfold f Q1
  compute_degree!

lemma hdeg_rhs : (X^29 - P1).natDegree = 29 := by
  unfold P1
  compute_degree!
