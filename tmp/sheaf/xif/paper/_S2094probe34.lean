import Mathlib

open Polynomial

local instance : Fact (Nat.Prime 29) := ⟨by norm_num⟩

noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

@[simp] lemma C_natCast_mod_of_ge (n : ℕ) (h : 29 ≤ n) :
    (C ((n : ℕ) : ZMod 29) : (ZMod 29)[X]) = C (((n % 29 : ℕ) : ZMod 29)) := by
  rw [C_inj, ZMod.natCast_eq_natCast_iff']
  rw [Nat.mod_eq_of_lt (Nat.mod_lt _ (by norm_num))]

def f : (ZMod 29)[X] :=
  C (((10 : ℕ) : ZMod 29)) + C (((24 : ℕ) : ZMod 29)) * X + C (((16 : ℕ) : ZMod 29)) * X^2 +
  C (((14 : ℕ) : ZMod 29)) * X^3 + C (((24 : ℕ) : ZMod 29)) * X^4 + C (((8 : ℕ) : ZMod 29)) * X^5 +
  C (((5 : ℕ) : ZMod 29)) * X^6 + C (((7 : ℕ) : ZMod 29)) * X^7 + C (((0 : ℕ) : ZMod 29)) * X^8 +
  C (((25 : ℕ) : ZMod 29)) * X^9 + C (((1 : ℕ) : ZMod 29)) * X^10

def P1 : (ZMod 29)[X] :=
  C (((13 : ℕ) : ZMod 29)) + C (((1 : ℕ) : ZMod 29)) * X + C (((26 : ℕ) : ZMod 29)) * X^2 +
  C (((24 : ℕ) : ZMod 29)) * X^3 + C (((4 : ℕ) : ZMod 29)) * X^4 + C (((10 : ℕ) : ZMod 29)) * X^5 +
  C (((25 : ℕ) : ZMod 29)) * X^6 + C (((23 : ℕ) : ZMod 29)) * X^7 + C (((18 : ℕ) : ZMod 29)) * X^8 +
  C (((20 : ℕ) : ZMod 29)) * X^9

def Q1 : (ZMod 29)[X] :=
  C (((19 : ℕ) : ZMod 29)) + C (((21 : ℕ) : ZMod 29)) * X + C (((21 : ℕ) : ZMod 29)) * X^2 +
  C (((3 : ℕ) : ZMod 29)) * X^3 + C (((23 : ℕ) : ZMod 29)) * X^4 + C (((18 : ℕ) : ZMod 29)) * X^5 +
  C (((28 : ℕ) : ZMod 29)) * X^6 + C (((16 : ℕ) : ZMod 29)) * X^7 + C (((10 : ℕ) : ZMod 29)) * X^8 +
  C (((13 : ℕ) : ZMod 29)) * X^9 + C (((7 : ℕ) : ZMod 29)) * X^10 + C (((8 : ℕ) : ZMod 29)) * X^11 +
  C (((6 : ℕ) : ZMod 29)) * X^12 + C (((24 : ℕ) : ZMod 29)) * X^13 + C (((2 : ℕ) : ZMod 29)) * X^14 +
  C (((21 : ℕ) : ZMod 29)) * X^15 + C (((28 : ℕ) : ZMod 29)) * X^16 + C (((16 : ℕ) : ZMod 29)) * X^17 +
  C (((4 : ℕ) : ZMod 29)) * X^18 + C (((1 : ℕ) : ZMod 29)) * X^19

example : X^29 - P1 = f * Q1 := by
  unfold f P1 Q1
  ring_nf
  simp only [mul_assoc]
  simp only [← C_mul, ← Nat.cast_mul]
  simp only [C_natCast_mod_of_ge]
  ring
