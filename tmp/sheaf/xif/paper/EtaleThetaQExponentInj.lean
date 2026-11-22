import Mathlib

noncomputable section

namespace LeanFormal.IUT.XiFPaper.EtaleThetaQExponentInj

abbrev HalfInt : Type := Rat

def thetaQExponent (n : Int) : HalfInt := (n : Rat) * ((n : Rat) + 1) / 2

theorem thetaQExponent_neg_succ (n : Int) :
    thetaQExponent (-n - 1) = thetaQExponent n := by
  unfold thetaQExponent
  rw [show (-n - 1 : Int) = -(n + 1) by ring]
  push_cast
  ring

theorem thetaQExponent_injective_nonneg {a b : Int}
    (ha : 0 <= a) (hb : 0 <= b) (h : thetaQExponent a = thetaQExponent b) :
    a = b := by
  have hfac : ((a : Rat) - (b : Rat)) * ((a : Rat) + (b : Rat) + 1) = 0 := by
    unfold thetaQExponent at h
    nlinarith
  rcases mul_eq_zero.mp hfac with h1 | h2
  · exact_mod_cast (sub_eq_zero.mp h1)
  · exfalso
    have : (a : Rat) + (b : Rat) + 1 = 0 := h2
    have : (0 : Rat) <= a := by exact_mod_cast ha
    have : (0 : Rat) <= b := by exact_mod_cast hb
    linarith

#check thetaQExponent_injective_nonneg

end LeanFormal.IUT.XiFPaper.EtaleThetaQExponentInj
