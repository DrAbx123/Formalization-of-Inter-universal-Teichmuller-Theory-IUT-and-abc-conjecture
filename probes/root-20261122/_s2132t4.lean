import Mathlib.Tactic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.Basic
open Polynomial
local instance : Fact (Nat.Prime 29) := ⟨by norm_num⟩

example : ((10 : ℤ[X]).map (Int.castRingHom (ZMod 29))) = (10 : (ZMod 29)[X]) := by norm_num
example : ((10 : ℤ[X]).map (Int.castRingHom (ZMod 29))) = (10 : (ZMod 29)[X]) := by simp
example : ((19 : ℤ[X]).map (Int.castRingHom (ZMod 29))) = (19 : (ZMod 29)[X]) := by norm_num
example (h : (120 : ZMod 29) = 3814697265625) : False := by norm_num at h
example : (120 : ZMod 29) =
    (3814697265625 : ZMod 29) := by norm_num
example : ((120 : ZMod 29) = 3814697265625) = False := by decide
